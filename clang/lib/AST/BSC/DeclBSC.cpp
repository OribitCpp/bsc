//===- DeclBSC.cpp - BSC Declaration AST Node Implementation --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the BSC related Decl classes.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/AST/ASTContext.h"
#include "clang/AST/BSC/DeclBSC.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Basic/Linkage.h"

using namespace clang;

//===----------------------------------------------------------------------===//
// BSCMethod Implementation
//===----------------------------------------------------------------------===//
BSCMethodDecl *BSCMethodDecl::Create(
    ASTContext &C, DeclContext *RD, SourceLocation StartLoc,
    const DeclarationNameInfo &NameInfo, QualType T, TypeSourceInfo *TInfo,
    StorageClass SC, bool UsesFPIntrinbool, bool isInline,
    ConstexprSpecKind ConstexprKind, SourceLocation EndLocation,
    Expr *TrailingRequiresClause, bool isAsync) {
  return new (C, RD) BSCMethodDecl(
      BSCMethod, C, RD, StartLoc, NameInfo, T, TInfo, SC, UsesFPIntrinbool,
      isInline, ConstexprKind, EndLocation, TrailingRequiresClause, isAsync);
}

BSCMethodDecl *BSCMethodDecl::CreateDeserialized(ASTContext &C, unsigned ID) {
  return new (C, ID) BSCMethodDecl(
      BSCMethod, C, nullptr, SourceLocation(), DeclarationNameInfo(),
      QualType(), nullptr, SC_None, false, false,
      ConstexprSpecKind::Unspecified, SourceLocation(), nullptr);
}

//===----------------------------------------------------------------------===//
// ImplTraitDecl Implementation
//===----------------------------------------------------------------------===//
TraitDecl::TraitDecl(Kind DK, const ASTContext &C, DeclContext *DC,
                     SourceLocation StartLoc, SourceLocation IdLoc,
                     IdentifierInfo *Id, TraitDecl *PrevDecl)
    : TagDecl(DK, TTK_Trait, C, DC, IdLoc, Id, PrevDecl, StartLoc) {
  assert(classof(static_cast<Decl *>(this)) && "Invalid Kind!");
}

TraitDecl *TraitDecl::Create(const ASTContext &C, DeclContext *DC,
                             SourceLocation StartLoc, SourceLocation IdLoc,
                             IdentifierInfo *Id, TraitDecl *PrevDecl,
                             bool DelayTypeCreation) {
  TraitDecl *R =
      new (C, DC) TraitDecl(Trait, C, DC, StartLoc, IdLoc, Id, PrevDecl);
  R->setMayHaveOutOfDateDef(C.getLangOpts().Modules);

  if (!DelayTypeCreation)
    C.getTypeDeclType(R, PrevDecl);
  return R;
}

TraitDecl *TraitDecl::CreateDeserialized(ASTContext &C, unsigned ID) {
  TraitDecl *R = new (C, ID) TraitDecl(Trait, C, nullptr, SourceLocation(),
                                       SourceLocation(), nullptr, nullptr);
  R->setMayHaveOutOfDateDef(C.getLangOpts().Modules);
  return R;
}

TraitTemplateDecl *TraitDecl::getDescribedTraitTemplate() const {
  return TemplateOrInstantiation.dyn_cast<TraitTemplateDecl *>();
}

void TraitDecl::setDescribedTraitTemplate(TraitTemplateDecl *Template) {
  TemplateOrInstantiation = Template;
}

MemberSpecializationInfo *TraitDecl::getMemberSpecializationInfo() const {
  return TemplateOrInstantiation.dyn_cast<MemberSpecializationInfo *>();
}

TemplateSpecializationKind TraitDecl::getTemplateSpecializationKind() const {
  if (const auto *Spec = dyn_cast<TraitTemplateSpecializationDecl>(this))
    return Spec->getSpecializationKind();

  if (MemberSpecializationInfo *MSInfo = getMemberSpecializationInfo())
    return MSInfo->getTemplateSpecializationKind();

  return TSK_Undeclared;
}

bool TraitDecl::isInjectedClassName() const {
  return isImplicit() && getDeclName() && getDeclContext()->isTrait() &&
         cast<TraitDecl>(getDeclContext())->getDeclName() == getDeclName();
}

TraitDecl::field_iterator TraitDecl::field_begin() const {
  return field_iterator(decl_iterator(FirstDecl));
}

void TraitDecl::completeDefinition() {
  assert(!isCompleteDefinition() && "Cannot redefine trait!");
  TagDecl::completeDefinition();
}

//===----------------------------------------------------------------------===//
// ImplTraitDecl Implementation
//===----------------------------------------------------------------------===//

ImplTraitDecl::ImplTraitDecl(ASTContext &C, DeclContext *DC,
                             SourceLocation StartLoc, SourceLocation IdLoc,
                             IdentifierInfo *Id, QualType T,
                             TypeSourceInfo *TInfo, StorageClass SC)
    : DeclaratorDecl(ImplTrait, DC, IdLoc, Id, T, TInfo, StartLoc),
      redeclarable_base(C) {}

ImplTraitDecl *ImplTraitDecl::Create(ASTContext &C, DeclContext *DC,
                                     SourceLocation StartL, SourceLocation IdL,
                                     IdentifierInfo *Id, QualType T,
                                     TypeSourceInfo *TInfo, StorageClass S) {
  return new (C, DC) ImplTraitDecl(C, DC, StartL, IdL, Id, T, TInfo, S);
}

ImplTraitDecl *ImplTraitDecl::CreateDeserialized(ASTContext &C, unsigned ID) {
  return new (C, ID)
      ImplTraitDecl(C, nullptr, SourceLocation(), SourceLocation(), nullptr,
                    QualType(), nullptr, SC_None);
}

SourceRange ImplTraitDecl::getSourceRange() const {
  return DeclaratorDecl::getSourceRange();
}

LanguageLinkage ImplTraitDecl::getLanguageLinkage() const {
  return LanguageLinkage::CLanguageLinkage;
}

bool ImplTraitDecl::isInExternCContext() const { return true; }

void ImplTraitDecl::setTraitDecl(TraitDecl *D) { ImplTraitDecl::TD = D; }

TraitDecl *ImplTraitDecl::getTraitDecl() { return ImplTraitDecl::TD; }

ImplTraitDecl *ImplTraitDecl::getCanonicalDecl() { return getFirstDecl(); }

//===----------------------------------------------------------------------===//
// TraitTemplateSpecializationDecl Implementation
//===----------------------------------------------------------------------===//

TraitTemplateSpecializationDecl::TraitTemplateSpecializationDecl(
    ASTContext &Context, Kind DK, TagKind TK, DeclContext *DC,
    SourceLocation StartLoc, SourceLocation IdLoc,
    TraitTemplateDecl *SpecializedTemplate, ArrayRef<TemplateArgument> Args,
    TraitTemplateSpecializationDecl *PrevDecl)
    : TraitDecl(DK, Context, DC, StartLoc, IdLoc,
                SpecializedTemplate->getIdentifier(), PrevDecl),
      SpecializedTemplate(SpecializedTemplate),
      TemplateArgs(TemplateArgumentList::CreateCopy(Context, Args)),
      SpecializationKind(TSK_Undeclared) {}

TraitTemplateSpecializationDecl::TraitTemplateSpecializationDecl(ASTContext &C,
                                                                 Kind DK)
    : TraitDecl(DK, C, nullptr, SourceLocation(), SourceLocation(), nullptr,
                nullptr),
      SpecializationKind(TSK_Undeclared) {}

TraitTemplateSpecializationDecl *TraitTemplateSpecializationDecl::Create(
    ASTContext &Context, TagKind TK, DeclContext *DC, SourceLocation StartLoc,
    SourceLocation IdLoc, TraitTemplateDecl *SpecializedTemplate,
    ArrayRef<TemplateArgument> Args,
    TraitTemplateSpecializationDecl *PrevDecl) {
  auto *Result = new (Context, DC) TraitTemplateSpecializationDecl(
      Context, TraitTemplateSpecialization, TK, DC, StartLoc, IdLoc,
      SpecializedTemplate, Args, PrevDecl);
  Result->setMayHaveOutOfDateDef(false);

  Context.getTypeDeclType(Result, PrevDecl);
  return Result;
}

TraitTemplateSpecializationDecl *
TraitTemplateSpecializationDecl::CreateDeserialized(ASTContext &C,
                                                    unsigned ID) {
  auto *Result = new (C, ID)
      TraitTemplateSpecializationDecl(C, TraitTemplateSpecialization);
  Result->setMayHaveOutOfDateDef(false);
  return Result;
}

TraitTemplateDecl *
TraitTemplateSpecializationDecl::getSpecializedTemplate() const {
  return SpecializedTemplate.get<TraitTemplateDecl *>();
}

BSCMethodDecl *RecordDecl::getBSCDestructor() const {
  ASTContext &Context = getASTContext();
  QualType ClassType = Context.getTypeDeclType(this);
  DeclarationName Name = Context.DeclarationNames.getCXXDestructorName(
      Context.getCanonicalType(ClassType));

  DeclContext::lookup_result R = lookup(Name);

  for (auto *Decl : R) {
    auto *DD = dyn_cast<BSCMethodDecl>(Decl);
    if (DD)
      return DD;
  }
  return nullptr;
}

#endif // ENABLE_BSC