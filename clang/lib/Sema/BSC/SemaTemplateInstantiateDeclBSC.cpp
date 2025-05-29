//===--- SemaTemplateInstantiateDeclBSC.cpp - BSC Template Decl Instantiation
//===/
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//===----------------------------------------------------------------------===/
//
//  This file implements BSC template instantiation for declarations.
//
//===----------------------------------------------------------------------===/

#if ENABLE_BSC

#include "TreeTransform.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/BSC/DeclBSC.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Template.h"

using namespace clang;

Decl *TemplateDeclInstantiator::VisitImplTraitDecl(ImplTraitDecl *D) {
  llvm_unreachable("ImplTraitDecl not supported yet");
}

Decl *TemplateDeclInstantiator::VisitTraitDecl(TraitDecl *D) {
  llvm_unreachable("There are only TraitDecls in BSC");
}

Decl *TemplateDeclInstantiator::VisitTraitTemplateDecl(TraitTemplateDecl *D) {
  llvm_unreachable("There are only TraitTemplateDecls in BSC");
}

Decl *TemplateDeclInstantiator::VisitTraitTemplateSpecializationDecl(
    TraitTemplateSpecializationDecl *D) {
  llvm_unreachable("There are only TraitTemplateSpecializationDecls in BSC");
}

/// Adjust the given function type for an instantiation of the
/// given declaration, to cope with modifications to the function's type that
/// aren't reflected in the type-source information.
/// \param D The declaration we're instantiating.
/// \param TInfo The already-instantiated type.
static QualType adjustFunctionTypeForInstantiation(ASTContext &Context,
                                                   FunctionDecl *D,
                                                   TypeSourceInfo *TInfo) {
  const FunctionProtoType *OrigFunc = D->getType()->castAs<FunctionProtoType>();
  const FunctionProtoType *NewFunc =
      TInfo->getType()->castAs<FunctionProtoType>();
  if (OrigFunc->getExtInfo() == NewFunc->getExtInfo())
    return TInfo->getType();

  FunctionProtoType::ExtProtoInfo NewEPI = NewFunc->getExtProtoInfo();
  NewEPI.ExtInfo = OrigFunc->getExtInfo();
  return Context.getFunctionType(NewFunc->getReturnType(),
                                 NewFunc->getParamTypes(), NewEPI);
}

bool TemplateDeclInstantiator::InitMethodInstantiation(BSCMethodDecl *New,
                                                       BSCMethodDecl *Tmpl) {
  if (InitFunctionInstantiation(New, Tmpl))
    return true;

  New->setAccess(Tmpl->getAccess());
  if (Tmpl->isVirtualAsWritten())
    New->setVirtualAsWritten(true);

  // FIXME: New needs a pointer to Tmpl
  return false;
}

Decl *TemplateDeclInstantiator::VisitBSCMethodDecl(
    BSCMethodDecl *D, TemplateParameterList *TemplateParams,
    Optional<const ASTTemplateArgumentListInfo *> ClassScopeSpecializationArgs,
    RewriteKind FunctionRewriteKind) {
  FunctionTemplateDecl *FunctionTemplate = D->getDescribedFunctionTemplate();
  if (FunctionTemplate && !TemplateParams) {
    // We are creating a function template specialization from a function
    // template. Check whether there is already a function template
    // specialization for this particular set of template arguments.
    ArrayRef<TemplateArgument> Innermost = TemplateArgs.getInnermost();

    void *InsertPos = nullptr;
    FunctionDecl *SpecFunc =
        FunctionTemplate->findSpecialization(Innermost, InsertPos);

    // If we already have a function template specialization, return it.
    if (SpecFunc)
      return SpecFunc;
  }

  bool MergeWithParentScope =
      (TemplateParams != nullptr) ||
      !(isa<Decl>(Owner) &&
        cast<Decl>(Owner)->isDefinedOutsideFunctionOrMethod());
  LocalInstantiationScope Scope(SemaRef, MergeWithParentScope);

  SmallVector<ParmVarDecl *, 4> Params;
  TypeSourceInfo *TInfo = SubstFunctionType(D, Params);
  if (!TInfo)
    return nullptr;
  QualType T = adjustFunctionTypeForInstantiation(SemaRef.Context, D, TInfo);

  if (TemplateParams && TemplateParams->size()) {
    auto *LastParam =
        dyn_cast<TemplateTypeParmDecl>(TemplateParams->asArray().back());
    if (LastParam && LastParam->isImplicit() &&
        LastParam->hasTypeConstraint()) {
      // In abbreviated templates, the type-constraints of invented template
      // type parameters are instantiated with the function type, invalidating
      // the TemplateParameterList which relied on the template type parameter
      // not having a type constraint. Recreate the TemplateParameterList with
      // the updated parameter list.
      TemplateParams = TemplateParameterList::Create(
          SemaRef.Context, TemplateParams->getTemplateLoc(),
          TemplateParams->getLAngleLoc(), TemplateParams->asArray(),
          TemplateParams->getRAngleLoc(), TemplateParams->getRequiresClause());
    }
  }

  NestedNameSpecifierLoc QualifierLoc = D->getQualifierLoc();
  if (QualifierLoc) {
    QualifierLoc =
        SemaRef.SubstNestedNameSpecifierLoc(QualifierLoc, TemplateArgs);
    if (!QualifierLoc)
      return nullptr;
  }

  // FIXME: Concepts: Do not substitute into constraint expressions
  Expr *TrailingRequiresClause = D->getTrailingRequiresClause();

  DeclContext *DC = Owner;

  DeclarationNameInfo NameInfo =
      SemaRef.SubstDeclarationNameInfo(D->getNameInfo(), TemplateArgs);

  if (FunctionRewriteKind != RewriteKind::None)
    adjustForRewrite(FunctionRewriteKind, D, T, TInfo, NameInfo);

  // Build the instantiated method declaration.
  RecordDecl *Record = cast<RecordDecl>(DC);
  BSCMethodDecl *Method = nullptr;

  SourceLocation StartLoc = D->getInnerLocStart();
  StorageClass SC = D->isStatic() ? SC_Static : SC_None;
  Method = BSCMethodDecl::Create(
      SemaRef.Context, Record, StartLoc, NameInfo, T, TInfo, SC,
      D->isInlineSpecified(), false, // isInline?
      D->getConstexprKind(), D->getEndLoc(), TrailingRequiresClause);
  Method->setHasThisParam(D->getHasThisParam());
  QualType ExtendedTy(Record->getTypeForDecl(), 0);
  Method->setExtendedType(ExtendedTy);
  Method->setExtentedTypeBeginLoc(D->getBeginLoc());
  Method->setDestructor(D->isDestructor());
  SemaRef.Context.BSCDeclContextMap[Record->getTypeForDecl()] = DC;

  if (D->isInlined())
    Method->setImplicitlyInline();

  if (QualifierLoc)
    Method->setQualifierInfo(QualifierLoc);

  if (TemplateParams) {
    // Our resulting instantiation is actually a function template, since we
    // are substituting only the outer template parameters. For example, given
    //
    //   template<typename T>
    //   struct X {
    //     template<typename U> void f(T, U);
    //   };
    //
    //   X<int> x;
    //
    // We are instantiating the member template "f" within X<int>, which means
    // substituting int for T, but leaving "f" as a member function template.
    // Build the function template itself.
    FunctionTemplate = FunctionTemplateDecl::Create(
        SemaRef.Context, Record, Method->getLocation(), Method->getDeclName(),
        TemplateParams, Method);
    if (D->isOutOfLine())
      FunctionTemplate->setLexicalDeclContext(D->getLexicalDeclContext());
    Method->setDescribedFunctionTemplate(FunctionTemplate);
  } else if (FunctionTemplate) {
    // Record this function template specialization.
    ArrayRef<TemplateArgument> Innermost = TemplateArgs.getInnermost();
    Method->setFunctionTemplateSpecialization(
        FunctionTemplate,
        TemplateArgumentList::CreateCopy(SemaRef.Context, Innermost),
        /*InsertPos=*/nullptr);
  } else {
    // Record that this is an instantiation of a member function.
    Method->setInstantiationOfMemberFunction(D, TSK_ImplicitInstantiation);
  }

  Method->setLexicalDeclContext(Owner);

  // Attach the parameters
  for (unsigned P = 0; P < Params.size(); ++P)
    Params[P]->setOwningFunction(Method);
  Method->setParams(Params);

  if (InitMethodInstantiation(Method, D))
    Method->setInvalidDecl();

  LookupResult Previous(SemaRef, NameInfo, Sema::LookupOrdinaryName,
                        Sema::ForExternalRedeclaration);

  bool IsExplicitSpecialization = false;

  // If the name of this function was written as a template-id, instantiate
  // the explicit template arguments.
  if (const ASTTemplateArgumentListInfo *Info =
          ClassScopeSpecializationArgs.value_or(
              D->getTemplateSpecializationArgsAsWritten())) {
    SemaRef.LookupQualifiedName(Previous, DC);

    TemplateArgumentListInfo ExplicitArgs(Info->getLAngleLoc(),
                                          Info->getRAngleLoc());
    if (SemaRef.SubstTemplateArguments(Info->arguments(), TemplateArgs,
                                       ExplicitArgs))
      return nullptr;

    if (SemaRef.CheckFunctionTemplateSpecialization(Method, &ExplicitArgs,
                                                    Previous))
      Method->setInvalidDecl();

    IsExplicitSpecialization = true;
  } else if (ClassScopeSpecializationArgs) {
    // Class-scope explicit specialization written without explicit template
    // arguments.
    SemaRef.LookupQualifiedName(Previous, DC);
    if (SemaRef.CheckFunctionTemplateSpecialization(Method, nullptr, Previous))
      Method->setInvalidDecl();

    IsExplicitSpecialization = true;
  } else if (!FunctionTemplate || TemplateParams) {
    SemaRef.LookupQualifiedName(Previous, Record);

    // In BSC, the previous declaration we find might be a tag type
    // (class or enum). In this case, the new declaration will hide the
    // tag type. Note that this does does not apply if we're declaring a
    // typedef.
    if (Previous.isSingleTagDecl())
      Previous.clear();
  }

  SemaRef.CheckFunctionDeclaration(nullptr, Method, Previous,
                                   IsExplicitSpecialization, false);

  Method->setAccess(D->getAccess());
  if (FunctionTemplate)
    FunctionTemplate->setAccess(Method->getAccess());

  // If this is an explicit specialization, mark the implicitly-instantiated
  // template specialization as being an explicit specialization too.
  // FIXME: Is this necessary?
  if (IsExplicitSpecialization)
    SemaRef.CompleteMemberSpecialization(Method, Previous);

  // If there's a function template, let our caller handle it.
  if (FunctionTemplate) {
    // do nothing

    // Don't hide a (potentially) valid declaration with an invalid one.
  } else if (Method->isInvalidDecl() && !Previous.empty()) {
    // do nothing

    // Otherwise, add the declaration.  We don't need to do this for
    // class-scope specializations because we'll have matched them with
    // the appropriate template.
  } else {
    Owner->addDecl(Method);
  }

  // PR17480: Honor the used attribute to instantiate member function
  // definitions
  if (Method->hasAttr<UsedAttr>()) {
    if (const auto *A = dyn_cast<RecordDecl>(Owner)) {
      SourceLocation Loc;
      if (const MemberSpecializationInfo *MSInfo =
              A->getMemberSpecializationInfo())
        Loc = MSInfo->getPointOfInstantiation();
      else if (const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(A))
        Loc = Spec->getPointOfInstantiation();
      SemaRef.MarkFunctionReferenced(Loc, Method);
    }
  }

  return Method;
}

Decl *TemplateDeclInstantiator::VisitBSCMethodDecl(BSCMethodDecl *D) {
  return VisitBSCMethodDecl(D, nullptr);
}

#endif