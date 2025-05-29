//===--- ParseDeclBSC.cpp - BSC Declaration Parsing -------------*- BSC -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file implements the BSC Declaration portions of the Parser interfaces.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/PrettyDeclStackTrace.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Sema/SemaDiagnostic.h"
#include "clang/Parse/Parser.h"
#include "clang/Parse/RAIIObjectsForParser.h"
#include "llvm/Support/TimeProfiler.h"
#include "clang/Sema/Lookup.h"

using namespace clang;

void Parser::ParseBSCScopeSpecifiers(DeclSpec &DS) {
  bool BSCScopeSpecFlag = true;
  ParseDeclarationSpecifiers(DS, ParsedTemplateInfo(), AS_none,
                             DeclSpecContext::DSC_normal, nullptr,
                             BSCScopeSpecFlag);
}

bool Parser::ParseTraitMemberDeclaratorBeforeInitializer(
    Declarator &DeclaratorInfo, VirtSpecifiers &VS, ExprResult &BitfieldSize,
    LateParsedAttrList &LateParsedAttrs) {
  if (Tok.isNot(tok::colon)) {
    DeclaratorInfo.setIsTraitMember(true);
    ParseDeclarator(DeclaratorInfo);
  } else {
    DeclaratorInfo.SetIdentifier(nullptr, Tok.getLocation());
  }

  if (!DeclaratorInfo.isFunctionDeclarator() && TryConsumeToken(tok::colon)) {
    assert(DeclaratorInfo.isPastIdentifier() &&
           "don't know where identifier would go yet?");
    BitfieldSize = ParseConstantExpression();
    if (BitfieldSize.isInvalid())
      SkipUntil(tok::comma, StopAtSemi | StopBeforeMatch);
  }
  if (!DeclaratorInfo.hasName() && BitfieldSize.isUnset()) {
    // If so, skip until the semi-colon or a }.
    SkipUntil(tok::r_brace, StopAtSemi | StopBeforeMatch);
    return true;
  }
  return false;
}

Parser::DeclGroupPtrTy
Parser::ParseTraitMemberDeclaration(ParsedAttributes &AccessAttrs) {
  ParenBraceBracketBalancer BalancerRAIIObj(*this);
  ParsedAttributes attrs(AttrFactory);
  ParsedAttributesView FnAttrs;
  // we need to keep these attributes for future diagnostic
  // before they are taken over by declaration specifier
  FnAttrs.addAll(attrs.begin(), attrs.end());
  FnAttrs.Range = attrs.Range;
  LateParsedAttrList CommonLateParsedAttrs;
  // decl-specifier-seq:
  // Parse the common declaration-specifiers piece
  ParsingDeclSpec DS(*this);
  DS.takeAttributesFrom(attrs);
  ParseDeclarationSpecifiers(DS, ParsedTemplateInfo(), AS_public,
                             DeclSpecContext::DSC_class,
                             &CommonLateParsedAttrs);
  if (TryConsumeToken(tok::semi)) {
    RecordDecl *AnonRecord = nullptr;
    Decl *TheDecl = Actions.ParsedFreeStandingDeclSpec(getCurScope(), AS_public,
                                                       DS, FnAttrs, AnonRecord);
    DS.complete(TheDecl);
    if (AnonRecord) {
      Decl *decls[] = {AnonRecord, TheDecl};
      return Actions.BuildDeclaratorGroup(decls);
    }
    return Actions.ConvertDeclToDeclGroup(TheDecl);
  }
  ParsingDeclarator DeclaratorInfo(*this, DS, attrs, DeclaratorContext::Member);
  VirtSpecifiers VS;
  // Hold late-parsed attributes so we can attach a Decl to them later.
  LateParsedAttrList LateParsedAttrs;
  SmallVector<Decl *, 8> DeclsInGroup;
  ExprResult BitfieldSize;
  ExprResult TrailingRequiresClause;
  ParseTraitMemberDeclaratorBeforeInitializer(DeclaratorInfo, VS, BitfieldSize,
                                              LateParsedAttrs);
  while (1) {
    NamedDecl *ThisDecl =
        Actions.ActOnTraitMemberDeclarator(getCurScope(), DeclaratorInfo);
    if (ThisDecl) {
      Actions.ProcessDeclAttributeList(getCurScope(), ThisDecl, AccessAttrs);
      if (!ThisDecl->isInvalidDecl()) {
        // Set the Decl for any late parsed attributes
        for (unsigned i = 0, ni = CommonLateParsedAttrs.size(); i < ni; ++i)
          CommonLateParsedAttrs[i]->addDecl(ThisDecl);
        for (unsigned i = 0, ni = LateParsedAttrs.size(); i < ni; ++i)
          LateParsedAttrs[i]->addDecl(ThisDecl);
      }
      Actions.FinalizeDeclaration(ThisDecl);
      DeclsInGroup.push_back(ThisDecl); // Put each Decl inside struct Foo
      if (DeclaratorInfo.isFunctionDeclarator() &&
          DeclaratorInfo.getDeclSpec().getStorageClassSpec() !=
              DeclSpec::SCS_typedef)
        HandleMemberFunctionDeclDelays(DeclaratorInfo, ThisDecl);
    }
    LateParsedAttrs.clear();
    DeclaratorInfo.complete(ThisDecl);
    // if we dont have a comma, it is either the end of the list (a, ';')
    // or an error, bail out
    SourceLocation CommaLoc;
    if (!TryConsumeToken(tok::comma, CommaLoc))
      break;
    if (Tok.isAtStartOfLine() &&
        !MightBeDeclarator(DeclaratorContext::Member)) {
      Diag(CommaLoc, diag::err_expected_semi_declaration)
          << FixItHint::CreateReplacement(CommaLoc, ";");
      break;
    }
    // Parse the next declarator
    DeclaratorInfo.clear();
    VS.clear();
    BitfieldSize = ExprResult(false);
    DeclaratorInfo.setCommaLoc(CommaLoc);
    if (ParseTraitMemberDeclaratorBeforeInitializer(
            DeclaratorInfo, VS, BitfieldSize, LateParsedAttrs))
      break;
  }
  return Actions.FinalizeDeclaratorGroup(getCurScope(), DS, DeclsInGroup);
}

void Parser::ParseTraitBody(SourceLocation TraitLoc,
                            SourceLocation AttrFixitLoc, Decl *TagDecl) {
  PrettyDeclStackTraceEntry CrashInfo(Actions.Context, TagDecl, TraitLoc,
                                      "parsing trait body");
  bool NonNestedClass = true;
  // Enter a scope for the class
  ParseScope ClassScope(this, Scope::ClassScope | Scope::DeclScope);

  // Note that we are parsing a new (potentially-nested) class definition
  ParsingClassDefinition ParsingDef(*this, TagDecl, NonNestedClass, false);
  if (TagDecl)
    Actions.ActOnTagStartDefinition(getCurScope(), TagDecl);
  if (!Tok.is(tok::l_brace)) {
    if (TagDecl)
      Actions.ActOnTagDefinitionError(getCurScope(), TagDecl);
    return;
  }
  BalancedDelimiterTracker T(*this, tok::l_brace);
  T.consumeOpen();
  ParsedAttributes AccessAttrs(AttrFactory);
  if (TagDecl) {
    // While we still have something to read. read the member-decls
    while (!tryParseMisplacedModuleImport() && Tok.isNot(tok::r_brace) &&
           Tok.isNot(tok::eof)) {
      // Each iter of this loop reads one member-declaration
      if (Tok.is(tok::semi)) {
        ConsumeExtraSemi(InsideStruct, DeclSpec::TST_trait);
        continue;
      }
      ParseTraitMemberDeclaration(AccessAttrs);
      MaybeDestroyTemplateIds();
      if (TryConsumeToken(tok::semi))
        continue;
    }
    T.consumeClose();
  } else {
    SkipUntil(tok::r_brace);
  }
  ParsedAttributes attrs(AttrFactory);
  if (TagDecl)
    Actions.ActOnFinishTraitMemberSpecification(TagDecl);
  if (TagDecl)
    Actions.ActOnTagFinishDefinition(getCurScope(), TagDecl, T.getRange());

  // Leave the trait scope
  ParsingDef.Pop();
  ClassScope.Exit();
}

// FIXME: ParseTraitSpecifier can be refactored, remove useless code
void Parser::ParseTraitSpecifier(SourceLocation StartLoc, DeclSpec &DS,
                                 const ParsedTemplateInfo &TemplateInfo,
                                 bool EnteringContext, DeclSpecContext DSC,
                                 ParsedAttributes &Attributes) {
  assert(getLangOpts().BSC &&
         "Error enter bsc trait specifier parsing function.");
  DeclSpec::TST TagType = DeclSpec::TST_trait;
  tok::TokenKind TagTokKind = tok::kw_trait;
  if (Tok.is(tok::code_completion)) {
    Actions.CodeCompleteTag(getCurScope(), TagType);
    return cutOffParsing();
  }
  ParsedAttributes attrs(AttrFactory);
  SourceLocation AttrFixitLoc = Tok.getLocation();
  IdentifierInfo *Name = nullptr;
  if (Tok.is(tok::identifier))
    Name = Tok.getIdentifierInfo();

  struct PreserveAtomicIdentifierInfoRAII {
    PreserveAtomicIdentifierInfoRAII(Token &Tok, bool Enabled)
        : AtomicII(nullptr) {
      if (!Enabled)
        return;
      assert(Tok.is(tok::kw__Atomic));
      AtomicII = Tok.getIdentifierInfo();
      AtomicII->revertTokenIDToIdentifier();
      Tok.setKind(tok::identifier);
    }
    ~PreserveAtomicIdentifierInfoRAII() {
      if (!AtomicII)
        return;
      AtomicII->revertIdentifierToTokenID(tok::kw__Atomic);
    }
    IdentifierInfo *AtomicII;
  };

  CXXScopeSpec &SS = DS.getTypeSpecScope();
  ColonProtectionRAIIObject X(*this);
  CXXScopeSpec Spec;
  bool HasValidSpec = true;
  const bool IsTemplated =
      (TemplateInfo.Kind != ParsedTemplateInfo::NonTemplate);

  if (ParseOptionalBSCGenericSpecifier(Spec, /*ObjectType=*/nullptr,
                                       /*ObjectHadErrors=*/false,
                                       EnteringContext, IsTemplated)) {
    DS.SetTypeSpecError();
    HasValidSpec = false;
  }

  if (Spec.isSet())
    if (Tok.isNot(tok::identifier) && Tok.isNot(tok::annot_template_id)) {
      Diag(Tok, diag::err_expected) << tok::identifier;
      HasValidSpec = false;
    }
  if (HasValidSpec)
    SS = Spec;

  TemplateParameterLists *TemplateParams = TemplateInfo.TemplateParams;

  auto RecoverFromUndeclaredTemplateName = [&](IdentifierInfo *Name,
                                               SourceLocation NameLoc,
                                               SourceRange TemplateArgRange,
                                               bool KnownUndeclared) {
    Diag(NameLoc, diag::err_explicit_spec_non_template)
        << (TemplateInfo.Kind == ParsedTemplateInfo::ExplicitInstantiation)
        << TagTokKind << Name << TemplateArgRange << KnownUndeclared;

    // Strip off the last template parameter list if it was empty, since
    // we've removed its template argument list.
    if (TemplateParams && TemplateInfo.LastParameterListWasEmpty) {
      if (TemplateParams->size() > 1) {
        TemplateParams->pop_back();
      } else {
        TemplateParams = nullptr;
        const_cast<ParsedTemplateInfo &>(TemplateInfo).Kind =
            ParsedTemplateInfo::NonTemplate;
      }
    } else if (TemplateInfo.Kind == ParsedTemplateInfo::ExplicitInstantiation) {
      // Pretend this is just a forward declaration.
      TemplateParams = nullptr;
      const_cast<ParsedTemplateInfo &>(TemplateInfo).Kind =
          ParsedTemplateInfo::NonTemplate;
      const_cast<ParsedTemplateInfo &>(TemplateInfo).TemplateLoc =
          SourceLocation();
      const_cast<ParsedTemplateInfo &>(TemplateInfo).ExternLoc =
          SourceLocation();
    }
  };

  SourceLocation NameLoc;
  TemplateIdAnnotation *TemplateId = nullptr;
  bool isParsingBSCTemplateTrait =
      Tok.is(tok::identifier) && NextToken().is(tok::less);
  if (Tok.is(tok::identifier)) {
    Name = Tok.getIdentifierInfo();
    NameLoc = ConsumeToken();

    // BSC Trait Template Declaration may have "<T>" syntax.
    //      This param list must been parsed, skip it.
    if (isParsingBSCTemplateTrait) {
      while (Tok.getKind() != tok::greater) {
        ConsumeToken();
      }
      if (Tok.is(tok::greater)) {
        ConsumeToken();
      } else {
        Diag(Tok.getLocation(), diag::err_expected_comma_greater);
      }
    }
  } else if (Tok.is(tok::annot_template_id)) {
    TemplateId = takeTemplateIdAnnotation(Tok);
    NameLoc = ConsumeAnnotationToken();

    if (TemplateId->Kind == TNK_Undeclared_template) {
      // Try to resolve the template name to a type template. May update Kind.
      Actions.ActOnUndeclaredTypeTemplateName(
          getCurScope(), TemplateId->Template, TemplateId->Kind, NameLoc, Name);
      if (TemplateId->Kind == TNK_Undeclared_template) {
        RecoverFromUndeclaredTemplateName(
            Name, NameLoc,
            SourceRange(TemplateId->LAngleLoc, TemplateId->RAngleLoc), true);
        TemplateId = nullptr;
      }
    }

    if (TemplateId && !TemplateId->mightBeType()) {
      // The template-name in the simple-template-id refers to
      // something other than a type template. Give an appropriate
      // error message and skip to the ';'.
      SourceRange Range(NameLoc);
      if (SS.isNotEmpty())
        Range.setBegin(SS.getBeginLoc());

      // FIXME: Name may be null here.
      Diag(TemplateId->LAngleLoc, diag::err_template_spec_syntax_non_template)
          << TemplateId->Name << static_cast<int>(TemplateId->Kind) << Range;

      DS.SetTypeSpecError();
      SkipUntil(tok::semi, StopBeforeMatch);
      return;
    }
  }

  const PrintingPolicy &Policy = Actions.getASTContext().getPrintingPolicy();
  Sema::TagUseKind TUK;
  if (isDefiningTypeSpecifierContext(DSC, false) == AllowDefiningTypeSpec::No)
    TUK = Sema::TUK_Reference;
  else if (Tok.is(tok::l_brace)) {
    TUK = Sema::TUK_Definition;
    // Trait can only be defined at top-level. So an error is required
    // when the depth of CurScope is greater than 0. However, for
    // generic trait, parsing generic parameters will enter TemplateParamScope
    // with a depth of 1, which needs to be allowed.
    if (Actions.getCurScope()->getDepth() > 0 &&
        !(!Actions.getCurScope()->getEntity() &&
          Actions.getCurScope()->getDepth() == 1)) {
      Diag(StartLoc, diag::err_trait_def_not_at_top_level);
      return;
    }
  } else if (!isTypeSpecifier(DSC) &&
             (Tok.is(tok::semi) ||
              (Tok.isAtStartOfLine() && !isValidAfterTypeSpecifier(false)))) {
    TUK = DS.isFriendSpecified() ? Sema::TUK_Friend : Sema::TUK_Declaration;
    if (Tok.isNot(tok::semi)) {
      const PrintingPolicy &PPol = Actions.getASTContext().getPrintingPolicy();
      // A semicolon was missing after this declaration. Diagnose and recover.
      ExpectAndConsume(tok::semi, diag::err_expected_after,
                       DeclSpec::getSpecifierName(TagType, PPol));
      PP.EnterToken(Tok, /*IsReinject*/ true);
      Tok.setKind(tok::semi);
    } else {
      std::string TraitName = "(null)";
      if (Name)
        TraitName = Name->getName().str();
      Diag(StartLoc, diag::err_invalid_trait) << TraitName;
    }
  } else
    TUK = Sema::TUK_Reference;

  if (TUK != Sema::TUK_Reference) {
    SourceRange AttrRange = Attributes.Range;
    if (AttrRange.isValid()) {
      Diag(AttrRange.getBegin(), diag::err_attributes_not_allowed)
          << AttrRange
          << FixItHint::CreateInsertionFromRange(
                 AttrFixitLoc, CharSourceRange(AttrRange, true))
          << FixItHint::CreateRemoval(AttrRange);
      attrs.takeAllFrom(Attributes);
    }
  }

  if (!Name && !TemplateId &&
      (DS.getTypeSpecType() == DeclSpec::TST_error ||
       TUK != Sema::TUK_Definition)) {
    if (DS.getTypeSpecType() != DeclSpec::TST_error) {
      Diag(StartLoc, diag::err_anon_type_definition)
          << DeclSpec::getSpecifierName(TagType, Policy);
    }
    if (TUK == Sema::TUK_Definition && Tok.is(tok::colon))
      SkipUntil(tok::semi, StopBeforeMatch);
    else
      SkipUntil(tok::comma, StopAtSemi);
    return;
  }

  DeclResult TagOrTempResult = true; // invalid
  TypeResult TypeResult = true;      // invalid
  bool Owned = false;
  Sema::SkipBodyInfo SkipBody;
  bool IsDependent = false;
  MultiTemplateParamsArg TParams;
  if (TUK != Sema::TUK_Reference && TemplateParams)
    TParams =
        MultiTemplateParamsArg(&(*TemplateParams)[0], TemplateParams->size());

  if (TemplateId) {
    ASTTemplateArgsPtr TemplateArgsPtr(TemplateId->getTemplateArgs(),
                                       TemplateId->NumArgs);
    if (TemplateId->isInvalid()) {
      // Can't build the declaration.
    } else if (TUK == Sema::TUK_Reference) {
      ProhibitCXX11Attributes(attrs, diag::err_attributes_not_allowed,
                              /*DiagnoseEmptyAttrs=*/true);
      TypeResult = Actions.ActOnTagTemplateIdType(
          TUK, TagType, StartLoc, SS, TemplateId->TemplateKWLoc,
          TemplateId->Template, TemplateId->TemplateNameLoc,
          TemplateId->LAngleLoc, TemplateArgsPtr, TemplateId->RAngleLoc);
    }
  } else {
    if (TUK != Sema::TUK_Declaration && TUK != Sema::TUK_Definition)
      ProhibitAttributes(attrs);

    stripTypeAttributesOffDeclSpec(attrs, DS, TUK);
    TagOrTempResult = Actions.ActOnTag(
        getCurScope(), TagType, TUK, StartLoc, SS, Name, NameLoc, attrs,
        AS_public, DS.getModulePrivateSpecLoc(), TParams, Owned, IsDependent,
        SourceLocation(), false, clang::TypeResult(),
        DSC == DeclSpecContext::DSC_type_specifier,
        DSC == DeclSpecContext::DSC_template_param ||
            DSC == DeclSpecContext::DSC_template_type_arg,
        &SkipBody);
    if (IsDependent) {
      assert(TUK == Sema::TUK_Reference);
      TypeResult = Actions.ActOnDependentTag(getCurScope(), TagType, TUK, SS,
                                             Name, StartLoc, NameLoc);
    }
  }

  if (TUK == Sema::TUK_Definition) {
    assert(Tok.is(tok::l_brace));
    ParseTraitBody(StartLoc, AttrFixitLoc, TagOrTempResult.get());
    if (SkipBody.CheckSameAsPrevious &&
        !Actions.ActOnDuplicateDefinition(TagOrTempResult.get(), SkipBody)) {
      DS.SetTypeSpecError();
      return;
    }
  }

  if (!TagOrTempResult.isInvalid())
    Actions.ProcessDeclAttributeDelayed(TagOrTempResult.get(), attrs);

  const char *PrevSpec = nullptr;
  unsigned DiagID;
  bool Result;
  if (!TypeResult.isInvalid()) {
    Result = DS.SetTypeSpecType(DeclSpec::TST_typename, StartLoc,
                                NameLoc.isValid() ? NameLoc : StartLoc,
                                PrevSpec, DiagID, TypeResult.get(), Policy);
  } else if (!TagOrTempResult.isInvalid()) {
    Result = DS.SetTypeSpecType(
        TagType, StartLoc, NameLoc.isValid() ? NameLoc : StartLoc, PrevSpec,
        DiagID, TagOrTempResult.get(), Owned, Policy);
  } else {
    DS.SetTypeSpecError();
    return;
  }

  if (Result)
    Diag(StartLoc, DiagID) << PrevSpec;

  // In a template-declaration which defines a class, no declarator is
  // permitted. eg. trait F<T> {}G; should report an error.
  if (TUK == Sema::TUK_Definition && !isTypeSpecifier(DSC) &&
      (TemplateInfo.Kind || !isValidAfterTypeSpecifier(false))) {
    if (Tok.isNot(tok::semi)) {
      const PrintingPolicy &PPol = Actions.getASTContext().getPrintingPolicy();
      ExpectAndConsume(tok::semi, diag::err_expected_after,
                       DeclSpec::getSpecifierName(TagType, PPol));
      PP.EnterToken(Tok, /*IsReinject=*/true);
      Tok.setKind(tok::semi);
    }
  }

  // desugar
  Decl *D = TagOrTempResult.get();
  if (TUK == Sema::TUK_Definition && D != nullptr && !D->isInvalidDecl()) {
    TraitDecl *TD = nullptr;
    if (auto *TTD = dyn_cast_or_null<TraitTemplateDecl>(D)) {
      TD = TTD->getTemplatedDecl();
    } else if (auto *TraitD = dyn_cast_or_null<TraitDecl>(D)) {
      TD = TraitD;
    }
    assert(TD && "No corresponding trait");

    RecordDecl *TraitVtableRD = Actions.ActOnDesugarVtableRecord(TD);
    RecordDecl *TraitRD = Actions.ActOnDesugarTraitRecord(TD, TraitVtableRD);
    TD->setTrait(TraitRD);
    RecordDecl *OwnedTraitRD = Actions.ActOnDesugarTraitRecord(TD, TraitVtableRD, true, false);
    TD->setOwnedTrait(OwnedTraitRD);
    RecordDecl *BorrowTraitRD = Actions.ActOnDesugarTraitRecord(TD, TraitVtableRD, false, true);
    TD->setBorrowTrait(BorrowTraitRD);
    TD->setVtable(TraitVtableRD);
  }
}

/// Parse an implementation trait declaration, for example:
/// - "impl trait T for int;"
/// - "impl trait Future<T> for int;"
Parser::DeclGroupPtrTy Parser::ParseImplTraitDeclaration() {
  ConsumeToken(); // Eat the "impl"
  SourceLocation TraitLoc = Tok.getLocation();
  TraitDecl *Trait = nullptr;
  IdentifierInfo *TraitII = nullptr;
  if (Tok.is(tok::kw_trait) && PP.LookAhead(0).is(tok::identifier))
    TraitII = PP.LookAhead(0).getIdentifierInfo();
  else { // For typedef
    NamedDecl *IIDecl = nullptr;
    LookupResult Result(Actions, Tok.getIdentifierInfo(), Tok.getLocation(), Sema::LookupOrdinaryName);
    Actions.LookupName(Result, getCurScope());
    if (Result.getResultKind() == LookupResult::Found) {
      IIDecl = Result.getFoundDecl();
      QualType QT;
      // TypedefNameDecl include TypedefDecl and TypeAliasDecl, for example:
      //   `typedef trait F G;` or `typedef trait F<int> G;` or `typedef G = trait F ;` or `typedef G = trait F<int>;`
      //   `impl G for int;`
      if (auto *TDD = dyn_cast<TypedefNameDecl>(IIDecl))
        QT = TDD->getUnderlyingType().getCanonicalType();
      // TypeAliasTemplateDecl for example:
      //   `typedef G<T> = trait F<T>;`
      //   `impl G<int> for int;`
      else if (auto *TATD = dyn_cast<TypeAliasTemplateDecl>(IIDecl)) {
        TypeAliasDecl *TAD = TATD->getTemplatedDecl();
        QT = TAD->getUnderlyingType().getCanonicalType();
      }
      if (auto TT = dyn_cast<TraitType>(QT))
        Trait = TT->getDecl();
      else if (auto TST = dyn_cast<TemplateSpecializationType>(QT)) {
        TemplateDecl *TempT = TST->getTemplateName().getAsTemplateDecl();
        Trait = dyn_cast_or_null<TraitDecl>(TempT->getTemplatedDecl());
      }
      if (Trait)
        TraitII = Trait->getIdentifier();
    }
  }
  DeclContext::lookup_result Decls = Actions.getASTContext().getTranslationUnitDecl()->lookup(TraitII);
  for (DeclContext::lookup_result::iterator I = Decls.begin(),
                                            E = Decls.end();
       I != E; ++I) {
    if (isa<TraitDecl>(*I)) {
      Trait = dyn_cast<TraitDecl>(*I);
    } else if (isa<TraitTemplateDecl>(*I)) {
      TraitTemplateDecl *TTD = dyn_cast<TraitTemplateDecl>(*I);
      Trait = TTD->getTemplatedDecl();
    }
  }
  if (!Trait) {
    Diag(Tok.getLocation(), diag::err_unexpected_token_for_impl_trait_decl);
    SkipUntil(tok::semi);
    return nullptr;
  }
  ParsingDeclSpec TraitDS(*this);
  ParseDeclarationSpecifiers(TraitDS);
  ParsedAttributes EmptyDeclSpecAttrs(AttrFactory);
  ParsingDeclarator TraitDeclarator(*this, TraitDS, EmptyDeclSpecAttrs,
                                    DeclaratorContext::File);

  if (Tok.is(tok::kw_for))
    ConsumeToken(); // eat token kw_for
  else {
    Diag(Tok.getLocation(), diag::err_unexpected_token_for_impl_trait_decl);
    SkipUntil(tok::semi);
    return nullptr;
  }

  ParsingDeclSpec TypeDS(*this);
  TypeDS.setImplTrait();
  ParseDeclarationSpecifiers(TypeDS);
  ParsingDeclarator TypeDeclarator(*this, TypeDS, EmptyDeclSpecAttrs,
                                   DeclaratorContext::File);
  ExpectAndConsumeSemi(diag::err_expected_semi_declaration);

  TraitDeclarator.SetIdentifier(TraitII, TraitLoc);
  TraitDeclarator.SetRangeEnd(TraitLoc);

  SmallVector<Decl *, 8> DeclsInGroup;
  // Step 1: Always produce ImplTraitDecl
  ImplTraitDecl *ITD = Actions.BuildImplTraitDecl(getCurScope(), TypeDeclarator,
                                                  TraitDeclarator, Trait);

  // Step 2: Desugar the ImplTraitDecl if we see it for the first time.
  // @code
  // impl trait TR for int;
  // impl trait TR for int; // OK, but useless, we don't desugar this line.
  // @endcode
  if (TraitDS.getTypeSpecType() == TST_error ||
      TypeDS.getTypeSpecType() == TST_error)
    return Actions.FinalizeDeclaratorGroup(getCurScope(), TypeDS, DeclsInGroup);

  VarDecl *DesugaredDecl = Actions.DesugarImplTrait(
      ITD, TypeDeclarator, TraitDeclarator, TypeDS.getBeginLoc());
  if (DesugaredDecl == nullptr) {
    return Actions.FinalizeDeclaratorGroup(getCurScope(), TypeDS, DeclsInGroup);
  }
  Actions.FinalizeDeclaration(DesugaredDecl);
  TypeDeclarator.complete(DesugaredDecl);
  DeclsInGroup.push_back(DesugaredDecl);

  return Actions.FinalizeDeclaratorGroup(getCurScope(), TypeDS, DeclsInGroup);
}

void Parser::TryParseBSCGenericClassSpecifier(ParsedAttributes &DeclSpecAttrs) {
  ParsingDeclSpec DS(*this);
  DS.takeAttributesFrom(DeclSpecAttrs);
  DeclSpecContext DSC = DeclSpecContext::DSC_normal;
  bool EnteringContext = false;
  SourceLocation StartLoc = Tok.getLocation();
  ParsedAttributes Attributes(AttrFactory);

  tok::TokenKind TagTokKind = Tok.getKind();
  DeclSpec::TST TagType = TagTokKind == tok::kw_struct ? DeclSpec::TST_struct : DeclSpec::TST_union;
  ConsumeToken();

  ParsedTemplateInfo TemplateInfo = ParsedTemplateInfo();
  const bool shouldDelayDiagsInTag =
      (TemplateInfo.Kind != ParsedTemplateInfo::NonTemplate);
  SuppressAccessChecks diagsFromTag(*this, shouldDelayDiagsInTag);

  ParsedAttributes attrs(AttrFactory);
  MaybeParseAttributes(PAKM_CXX11 | PAKM_Declspec | PAKM_GNU, attrs);
  SourceLocation AttrFixitLoc = Tok.getLocation();

  struct PreserveAtomicIdentifierInfoRAII {
    PreserveAtomicIdentifierInfoRAII(Token &Tok, bool Enabled)
        : AtomicII(nullptr) {
      if (!Enabled)
        return;
      assert(Tok.is(tok::kw__Atomic));
      AtomicII = Tok.getIdentifierInfo();
      AtomicII->revertTokenIDToIdentifier();
      Tok.setKind(tok::identifier);
    }
    ~PreserveAtomicIdentifierInfoRAII() {
      if (!AtomicII)
        return;
      AtomicII->revertIdentifierToTokenID(tok::kw__Atomic);
    }
    IdentifierInfo *AtomicII;
  };

  CXXScopeSpec &SS = DS.getTypeSpecScope();
  ColonProtectionRAIIObject X(*this);
  CXXScopeSpec Spec;
  bool HasValidSpec = true;

  if (ParseOptionalBSCGenericSpecifier(
          Spec, /*ObjectType=*/nullptr,
          /*ObjectHadErrors=*/false, EnteringContext, shouldDelayDiagsInTag)) {
    DS.SetTypeSpecError();
    HasValidSpec = false;
  }

  if (Spec.isSet())
    if (Tok.isNot(tok::identifier) && Tok.isNot(tok::annot_template_id)) {
      Diag(Tok, diag::err_expected) << tok::identifier;
      HasValidSpec = false;
    }
  if (HasValidSpec)
    SS = Spec;

  TemplateParameterLists *TemplateParams = TemplateInfo.TemplateParams;

  auto RecoverFromUndeclaredTemplateName = [&](IdentifierInfo *Name,
                                               SourceLocation NameLoc,
                                               SourceRange TemplateArgRange,
                                               bool KnownUndeclared) {
    Diag(NameLoc, diag::err_explicit_spec_non_template)
        << (TemplateInfo.Kind == ParsedTemplateInfo::ExplicitInstantiation)
        << TagTokKind << Name << TemplateArgRange << KnownUndeclared;

    // Strip off the last template parameter list if it was empty, since
    // we've removed its template argument list.
    if (TemplateParams && TemplateInfo.LastParameterListWasEmpty) {
      if (TemplateParams->size() > 1) {
        TemplateParams->pop_back();
      } else {
        TemplateParams = nullptr;
        const_cast<ParsedTemplateInfo &>(TemplateInfo).Kind =
            ParsedTemplateInfo::NonTemplate;
      }
    } else if (TemplateInfo.Kind == ParsedTemplateInfo::ExplicitInstantiation) {
      // Pretend this is just a forward declaration.
      TemplateParams = nullptr;
      const_cast<ParsedTemplateInfo &>(TemplateInfo).Kind =
          ParsedTemplateInfo::NonTemplate;
      const_cast<ParsedTemplateInfo &>(TemplateInfo).TemplateLoc =
          SourceLocation();
      const_cast<ParsedTemplateInfo &>(TemplateInfo).ExternLoc =
          SourceLocation();
    }
  };

  // Parse the (optional) class name or simple-template-id.
  IdentifierInfo *Name = nullptr;
  SourceLocation NameLoc = Tok.getLocation();
  TemplateIdAnnotation *TemplateId = nullptr;
  if (Tok.is(tok::identifier)) {
    Name = Tok.getIdentifierInfo();
  } else if (Tok.is(tok::annot_template_id)) {
    TemplateId = takeTemplateIdAnnotation(Tok);
    if (TemplateId->Kind == TNK_Undeclared_template) {
      // Try to resolve the template name to a type template. May update Kind.
      Actions.ActOnUndeclaredTypeTemplateName(
          getCurScope(), TemplateId->Template, TemplateId->Kind, NameLoc, Name);
      if (TemplateId->Kind == TNK_Undeclared_template) {
        RecoverFromUndeclaredTemplateName(
            Name, NameLoc,
            SourceRange(TemplateId->LAngleLoc, TemplateId->RAngleLoc), true);
        TemplateId = nullptr;
      }
    }

    if (TemplateId && !TemplateId->mightBeType()) {
      // The template-name in the simple-template-id refers to
      // something other than a type template. Give an appropriate
      // error message and skip to the ';'.
      SourceRange Range(NameLoc);
      if (SS.isNotEmpty())
        Range.setBegin(SS.getBeginLoc());

      // FIXME: Name may be null here.
      Diag(TemplateId->LAngleLoc, diag::err_template_spec_syntax_non_template)
          << TemplateId->Name << static_cast<int>(TemplateId->Kind) << Range;

      DS.SetTypeSpecError();
      SkipUntil(tok::semi, StopBeforeMatch);
      return;
    }
  }

  const PrintingPolicy &Policy = Actions.getASTContext().getPrintingPolicy();
  Sema::TagUseKind TUK;
  if (isDefiningTypeSpecifierContext(DSC, false) == AllowDefiningTypeSpec::No)
    TUK = Sema::TUK_Reference;
  else if (Tok.is(tok::l_brace))
    TUK = Sema::TUK_Definition;
  else if (!isTypeSpecifier(DSC) &&
            (Tok.is(tok::semi) ||
              (Tok.isAtStartOfLine() && !isValidAfterTypeSpecifier(false)))) {
    TUK = DS.isFriendSpecified() ? Sema::TUK_Friend : Sema::TUK_Declaration;
    if (Tok.isNot(tok::semi)) {
      const PrintingPolicy &PPol = Actions.getASTContext().getPrintingPolicy();
      // A semicolon was missing after this declaration. Diagnose and recover.
      ExpectAndConsume(tok::semi, diag::err_expected_after,
                       DeclSpec::getSpecifierName(TagType, PPol));
      PP.EnterToken(Tok, /*IsReinject*/ true);
      Tok.setKind(tok::semi);
    }
  } else
    TUK = Sema::TUK_Reference;

  if (TUK != Sema::TUK_Reference) {
    SourceRange AttrRange = Attributes.Range;
    if (AttrRange.isValid()) {
      Diag(AttrRange.getBegin(), diag::err_attributes_not_allowed)
          << AttrRange
          << FixItHint::CreateInsertionFromRange(
                 AttrFixitLoc, CharSourceRange(AttrRange, true))
          << FixItHint::CreateRemoval(AttrRange);
      attrs.takeAllFrom(Attributes);
    }
  }

  if (!Name && !TemplateId &&
      (DS.getTypeSpecType() == DeclSpec::TST_error ||
      TUK != Sema::TUK_Definition)) {
    if (DS.getTypeSpecType() != DeclSpec::TST_error) {
      Diag(StartLoc, diag::err_anon_type_definition)
          << DeclSpec::getSpecifierName(TagType, Policy);
    }
    if (TUK == Sema::TUK_Definition && Tok.is(tok::colon))
      SkipUntil(tok::semi, StopBeforeMatch);
    else
      SkipUntil(tok::comma, StopAtSemi);
    return;
  }

  DeclResult TagOrTempResult = true; // invalid
  TypeResult TypeResult = true;      // invalid

  bool Owned = false;
  Sema::SkipBodyInfo SkipBody;
  bool IsDependent = false;
  MultiTemplateParamsArg TParams;
  if (TUK != Sema::TUK_Reference && TemplateParams)
    TParams =
        MultiTemplateParamsArg(&(*TemplateParams)[0], TemplateParams->size());

  if (TemplateId) {
    ASTTemplateArgsPtr TemplateArgsPtr(TemplateId->getTemplateArgs(),
                                      TemplateId->NumArgs);
    if (TemplateId->isInvalid()) {
      // Can't build the declaration.
    } else if (TUK == Sema::TUK_Reference) {
      ProhibitCXX11Attributes(attrs, diag::err_attributes_not_allowed,
                              /*DiagnoseEmptyAttrs=*/true);
      TypeResult = Actions.ActOnTagTemplateIdType(
          TUK, TagType, StartLoc, SS, TemplateId->TemplateKWLoc,
          TemplateId->Template, TemplateId->TemplateNameLoc,
          TemplateId->LAngleLoc, TemplateArgsPtr, TemplateId->RAngleLoc);
    }
  } else {
    if (TUK != Sema::TUK_Declaration && TUK != Sema::TUK_Definition)
      ProhibitAttributes(attrs);

    stripTypeAttributesOffDeclSpec(attrs, DS, TUK);
    TagOrTempResult = Actions.ActOnTag(
        getCurScope(), TagType, TUK, StartLoc, SS, Name, NameLoc, attrs,
        AS_public, DS.getModulePrivateSpecLoc(), TParams, Owned, IsDependent,
        SourceLocation(), false, clang::TypeResult(),
        DSC == DeclSpecContext::DSC_type_specifier,
        DSC == DeclSpecContext::DSC_template_param ||
            DSC == DeclSpecContext::DSC_template_type_arg,
        &SkipBody);
    if (IsDependent) {
      assert(TUK == Sema::TUK_Reference);
      TypeResult = Actions.ActOnDependentTag(getCurScope(), TagType, TUK, SS,
                                             Name, StartLoc, NameLoc);
    }
  }

  if (!TagOrTempResult.isInvalid())
    Actions.ProcessDeclAttributeDelayed(TagOrTempResult.get(), attrs);

  const char *PrevSpec = nullptr;
  unsigned DiagID;
  bool Result;
  if (!TypeResult.isInvalid()) {
    Result = DS.SetTypeSpecType(DeclSpec::TST_typename, StartLoc,
                                NameLoc.isValid() ? NameLoc : StartLoc,
                                PrevSpec, DiagID, TypeResult.get(), Policy);
  } else if (!TagOrTempResult.isInvalid()) {
    Result = DS.SetTypeSpecType(
        TagType, StartLoc, NameLoc.isValid() ? NameLoc : StartLoc, PrevSpec,
        DiagID, TagOrTempResult.get(), Owned, Policy);
  } else {
    DS.SetTypeSpecError();
    return;
  }

  if (Result)
    Diag(StartLoc, DiagID) << PrevSpec;

  // In a template-declaration which defines a class, no declarator is
  // permitted.
  if (TUK == Sema::TUK_Definition && !isTypeSpecifier(DSC) &&
      (TemplateInfo.Kind || !isValidAfterTypeSpecifier(false))) {
    if (Tok.isNot(tok::semi)) {
      const PrintingPolicy &PPol = Actions.getASTContext().getPrintingPolicy();
      ExpectAndConsume(tok::semi, diag::err_expected_after,
                      DeclSpec::getSpecifierName(TagType, PPol));
      PP.EnterToken(Tok, /*IsReinject=*/true);
      Tok.setKind(tok::semi);
    }
  }
}
NamedDecl *Parser::ParseBSCInlineMethodDef(
    AccessSpecifier AS, const ParsedAttributesView &AccessAttrs,
    ParsingDeclarator &D, const ParsedTemplateInfo &TemplateInfo) {
  assert(D.isFunctionDeclarator() && "This isn't a function declarator!");
  assert(Tok.isOneOf(tok::l_brace, tok::colon, tok::kw_try, tok::equal) &&
         "Current token not a '{', ':', '=', or 'try'!");

  MultiTemplateParamsArg TemplateParams(
      TemplateInfo.TemplateParams ? TemplateInfo.TemplateParams->data()
                                  : nullptr,
      TemplateInfo.TemplateParams ? TemplateInfo.TemplateParams->size() : 0);

  NamedDecl *FnD = Actions.ActOnBSCMemberDeclarator(getCurScope(), AS, D,
                                                    TemplateParams, nullptr);
  if (FnD) {
    Actions.ProcessDeclAttributeList(getCurScope(), FnD, AccessAttrs);
  }

  if (FnD)
    HandleMemberFunctionDeclDelays(D, FnD);

  D.complete(FnD);

  if (SkipFunctionBodies && (!FnD || Actions.canSkipFunctionBody(FnD)) &&
      trySkippingFunctionBody()) {
    Actions.ActOnSkippedFunctionBody(FnD);
    return FnD;
  }

  // In delayed template parsing mode, if we are within a class template
  // or if we are about to parse function member template then consume
  // the tokens and store them for parsing at the end of the translation unit.
  if (getLangOpts().DelayedTemplateParsing &&
      D.getFunctionDefinitionKind() == FunctionDefinitionKind::Definition &&
      !D.getDeclSpec().hasConstexprSpecifier() &&
      !(FnD && FnD->getAsFunction() &&
        FnD->getAsFunction()->getReturnType()->getContainedAutoType()) &&
      ((Actions.CurContext->isDependentContext() ||
        (TemplateInfo.Kind != ParsedTemplateInfo::NonTemplate &&
         TemplateInfo.Kind != ParsedTemplateInfo::ExplicitSpecialization)) &&
       !Actions.IsInsideALocalClassWithinATemplateFunction())) {
    CachedTokens Toks;
    LexTemplateFunctionForLateParsing(Toks);

    if (FnD) {
      FunctionDecl *FD = FnD->getAsFunction();
      Actions.CheckForFunctionRedefinition(FD);
      Actions.MarkAsLateParsedTemplate(FD, FnD, Toks);
    }

    return FnD;
  }

  // Consume the tokens and store them for later parsing.

  LexedMethod *LM = new LexedMethod(this, FnD);
  getCurrentClass().LateParsedDeclarations.push_back(LM);
  CachedTokens &Toks = LM->Toks;

  // Consume everything up to (and including) the left brace of the
  // function body.
  if (ConsumeAndStoreFunctionPrologue(Toks)) {
    // We didn't find the left-brace we expected after the
    // constructor initializer.

    // If we're code-completing and the completion point was in the broken
    // initializer, we want to parse it even though that will fail.
    if (PP.isCodeCompletionEnabled() &&
        llvm::any_of(Toks, [](const Token &Tok) {
          return Tok.is(tok::code_completion);
        })) {
      // If we gave up at the completion point, the initializer list was
      // likely truncated, so don't eat more tokens. We'll hit some extra
      // errors, but they should be ignored in code completion.
      return FnD;
    }

    // We already printed an error, and it's likely impossible to recover,
    // so don't try to parse this method later.
    // Skip over the rest of the decl and back to somewhere that looks
    // reasonable.
    SkipMalformedDecl();
    delete getCurrentClass().LateParsedDeclarations.back();
    getCurrentClass().LateParsedDeclarations.pop_back();
    return FnD;
  } else {
    // Consume everything up to (and including) the matching right brace.
    ConsumeAndStoreUntil(tok::r_brace, Toks, /*StopAtSemi=*/false);
  }

  if (FnD) {
    FunctionDecl *FD = FnD->getAsFunction();
    // Track that this function will eventually have a body; Sema needs
    // to know this.
    Actions.CheckForFunctionRedefinition(FD);
    FD->setWillHaveBody(true);
  } else {
    // If semantic analysis could not build a function declaration,
    // just throw away the late-parsed declaration.
    delete getCurrentClass().LateParsedDeclarations.back();
    getCurrentClass().LateParsedDeclarations.pop_back();
  }

  return FnD;
}

Parser::DeclGroupPtrTy Parser::ParseBSCClassMemberDeclarationWithPragmas(
    AccessSpecifier &AS, ParsedAttributes &AccessAttrs, DeclSpec::TST TagType,
    Decl *TagDecl) {
  ParenBraceBracketBalancer BalancerRAIIObj(*this);

  switch (Tok.getKind()) {
  case tok::kw___if_exists:
  case tok::kw___if_not_exists:
    ParseMicrosoftIfExistsClassDeclaration(TagType, AccessAttrs, AS);
    return nullptr;

  case tok::semi:
    // Check for extraneous top-level semicolon.
    ConsumeExtraSemi(InsideStruct, TagType);
    return nullptr;

    // Handle pragmas that can appear as member declarations.
  case tok::annot_pragma_vis:
    HandlePragmaVisibility();
    return nullptr;
  case tok::annot_pragma_pack:
    HandlePragmaPack();
    return nullptr;
  case tok::annot_pragma_align:
    HandlePragmaAlign();
    return nullptr;
  case tok::annot_pragma_ms_pointers_to_members:
    HandlePragmaMSPointersToMembers();
    return nullptr;
  case tok::annot_pragma_ms_pragma:
    HandlePragmaMSPragma();
    return nullptr;
  case tok::annot_pragma_ms_vtordisp:
    HandlePragmaMSVtorDisp();
    return nullptr;
  case tok::annot_pragma_dump:
    HandlePragmaDump();
    return nullptr;

  case tok::kw_private:
    // FIXME: We don't accept GNU attributes on access specifiers in OpenCL mode
    // yet.
    if (getLangOpts().OpenCL && !NextToken().is(tok::colon))
      return ParseCXXClassMemberDeclaration(AS, AccessAttrs);
    LLVM_FALLTHROUGH;
  case tok::kw_public: {
    AccessSpecifier NewAS = getAccessSpecifierIfPresent();
    assert(NewAS != AS_none);
    // Current token is a C++ access specifier.
    AS = NewAS;
    SourceLocation ASLoc = Tok.getLocation();
    unsigned TokLength = Tok.getLength();
    ConsumeToken();
    AccessAttrs.clear();
    MaybeParseGNUAttributes(AccessAttrs);

    SourceLocation EndLoc;
    if (TryConsumeToken(tok::colon, EndLoc)) {
    } else if (TryConsumeToken(tok::semi, EndLoc)) {
      Diag(EndLoc, diag::err_expected)
          << tok::colon << FixItHint::CreateReplacement(EndLoc, ":");
    } else {
      EndLoc = ASLoc.getLocWithOffset(TokLength);
      Diag(EndLoc, diag::err_expected)
          << tok::colon << FixItHint::CreateInsertion(EndLoc, ":");
    }

    if (Actions.ActOnAccessSpecifier(NewAS, ASLoc, EndLoc, AccessAttrs)) {
      // found another attribute than only annotations
      AccessAttrs.clear();
    }

    return nullptr;
  }

  case tok::annot_attr_openmp:
  case tok::annot_pragma_openmp:
    return ParseOpenMPDeclarativeDirectiveWithExtDecl(
        AS, AccessAttrs, /*Delayed=*/true, TagType, TagDecl);

  default:
    if (tok::isPragmaAnnotation(Tok.getKind())) {
      Diag(Tok.getLocation(), diag::err_pragma_misplaced_in_decl)
          << DeclSpec::getSpecifierName(
                 TagType, Actions.getASTContext().getPrintingPolicy());
      ConsumeAnnotationToken();
      return nullptr;
    }
    return ParseBSCClassMemberDeclaration(AS, AccessAttrs);
  }
}
// map to ParseStructUnionBody
void Parser::ParseBSCMemberSpecification(SourceLocation RecordLoc,
                                         SourceLocation AttrFixitLoc,
                                         ParsedAttributes &Attrs,
                                         unsigned TagType, Decl *TagDecl) {
  assert((TagType == DeclSpec::TST_class || TagType == DeclSpec::TST_struct) &&
         "Invalid TagType!");

  llvm::TimeTraceScope TimeScope("ParseClass", [&]() {
    if (auto *TD = dyn_cast_or_null<NamedDecl>(TagDecl))
      return TD->getQualifiedNameAsString();
    return std::string("<anonymous>");
  });

  PrettyDeclStackTraceEntry CrashInfo(Actions.Context, TagDecl, RecordLoc,
                                      "parsing class body");

  // Enter a scope for the class.
  ParseScope ClassScope(this, Scope::ClassScope | Scope::DeclScope);

  // Note that we are parsing a new (potentially-nested) class definition.
  ParsingClassDefinition ParsingDef(*this, TagDecl, true, false);

  if (TagDecl)
    Actions.ActOnTagStartDefinition(getCurScope(), TagDecl);

  assert(Tok.is(tok::l_brace));
  BalancedDelimiterTracker T(*this, tok::l_brace);
  T.consumeOpen();

  if (TagDecl)
    Actions.ActOnStartBSCMemberDeclarations(getCurScope(), TagDecl,
                                            T.getOpenLocation());

  // C++ 11p3: Members of a class defined with the keyword class are private
  // by default. Members of a class defined with the keywords struct or union
  // are public by default.
  // HLSL: In HLSL members of a class are public by default.
  AccessSpecifier CurAS = AS_private;
  ParsedAttributes AccessAttrs(AttrFactory);

  if (TagDecl) {
    // While we still have something to read, read the member-declarations.
    while (!tryParseMisplacedModuleImport() && Tok.isNot(tok::r_brace) &&
           Tok.isNot(tok::eof)) {
      // Each iteration of this loop reads one member-declaration.
      ParseBSCClassMemberDeclarationWithPragmas(
          CurAS, AccessAttrs, static_cast<DeclSpec::TST>(TagType), TagDecl);
      MaybeDestroyTemplateIds();
    }
    T.consumeClose();
  } else {
    SkipUntil(tok::r_brace);
  }

  // If attributes exist after class contents, parse them.
  ParsedAttributes attrs(AttrFactory);
  MaybeParseGNUAttributes(attrs);

  if (TagDecl)
    Actions.ActOnFinishBSCMemberSpecification(getCurScope(), RecordLoc, TagDecl,
                                              T.getOpenLocation(),
                                              T.getCloseLocation(), attrs);

  // C++11 [class.mem]p2:
  //   Within the class member-specification, the class is regarded as complete
  //   within function bodies, default arguments, exception-specifications, and
  //   brace-or-equal-initializers for non-static data members (including such
  //   things in nested classes).
  if (TagDecl) {
    // We are not inside a nested class. This class and its nested classes
    // are complete and we can parse the delayed portions of method
    // declarations and the lexed inline method definitions, along with any
    // delayed attributes.

    SourceLocation SavedPrevTokLocation = PrevTokLocation;
    ParseLexedPragmas(getCurrentClass());
    ParseLexedAttributes(getCurrentClass());
    ParseLexedMethodDeclarations(getCurrentClass());

    // We've finished with all pending member declarations.
    ParseLexedMethodDefs(getCurrentClass());
    PrevTokLocation = SavedPrevTokLocation;

    // We've finished parsing everything, including default argument
    // initializers.
    Actions.ActOnFinishCXXNonNestedClass();
  }

  if (TagDecl)
    Actions.ActOnTagFinishDefinition(getCurScope(), TagDecl, T.getRange());

  // Leave the class scope.
  ParsingDef.Pop();
  ClassScope.Exit();
}

Parser::DeclGroupPtrTy
Parser::ParseBSCClassMemberDeclaration(AccessSpecifier AS,
                                       ParsedAttributes &AccessAttrs,
                                       const ParsedTemplateInfo &TemplateInfo,
                                       ParsingDeclRAIIObject *TemplateDiags) {
  if (Tok.is(tok::at)) { // TODO why not @def
    Diag(Tok, diag::err_at_in_class);

    ConsumeToken();
    SkipUntil(tok::r_brace, StopAtSemi);
    return nullptr;
  }

  // Turn on colon protection early, while parsing declspec, although there is
  // nothing to protect there. It prevents from false errors if error recovery
  // incorrectly determines where the declspec ends, as in the example:
  //   struct A { enum class B { C }; };
  //   const int C = 4;
  //   struct D { A::B : C; };
  ColonProtectionRAIIObject X(*this);

  // Access declarations.
  bool MalformedTypeSpec = false;
  if (!TemplateInfo.Kind && Tok.isOneOf(tok::identifier, tok::coloncolon)) {
    if (TryAnnotateCXXScopeToken())
      MalformedTypeSpec = true;

    bool isAccessDecl;
    if (Tok.isNot(tok::annot_cxxscope))
      isAccessDecl = false;
    else if (NextToken().is(tok::identifier))
      isAccessDecl = GetLookAheadToken(2).is(tok::semi);
    else
      isAccessDecl = NextToken().is(tok::kw_operator);

    if (isAccessDecl) {
      // Collect the scope specifier token we annotated earlier.
      CXXScopeSpec SS;
      ParseOptionalCXXScopeSpecifier(SS, /*ObjectType=*/nullptr,
                                     /*ObjectHasErrors=*/false,
                                     /*EnteringContext=*/false);

      if (SS.isInvalid()) {
        SkipUntil(tok::semi);
        return nullptr;
      }

      // Try to parse an unqualified-id.
      SourceLocation TemplateKWLoc;
      UnqualifiedId Name;
      if (ParseUnqualifiedId(SS, /*ObjectType=*/nullptr,
                             /*ObjectHadErrors=*/false, false, true, true,
                             false, &TemplateKWLoc, Name)) {
        SkipUntil(tok::semi);
        return nullptr;
      }

      // TODO: recover from mistakenly-qualified operator declarations.
      if (ExpectAndConsume(tok::semi, diag::err_expected_after,
                           "access declaration")) {
        SkipUntil(tok::semi);
        return nullptr;
      }

      // FIXME: We should do something with the 'template' keyword here.
      return DeclGroupPtrTy::make(DeclGroupRef(Actions.ActOnUsingDeclaration(
          getCurScope(), AS, /*UsingLoc*/ SourceLocation(),
          /*TypenameLoc*/ SourceLocation(), SS, Name,
          /*EllipsisLoc*/ SourceLocation(),
          /*AttrList*/ ParsedAttributesView())));
    }
  }

  // static_assert-declaration. A templated static_assert declaration is
  // diagnosed in Parser::ParseSingleDeclarationAfterTemplate.
  if (!TemplateInfo.Kind &&
      Tok.isOneOf(tok::kw_static_assert, tok::kw__Static_assert)) {
    SourceLocation DeclEnd;
    return DeclGroupPtrTy::make(
        DeclGroupRef(ParseStaticAssertDeclaration(DeclEnd)));
  }

  // Handle:  member-declaration ::= '__extension__' member-declaration
  if (Tok.is(tok::kw___extension__)) {
    // __extension__ silences extension warnings in the subexpression.
    ExtensionRAIIObject O(Diags); // Use RAII to do this.
    ConsumeToken();
    return ParseCXXClassMemberDeclaration(AS, AccessAttrs, TemplateInfo,
                                          TemplateDiags);
  }

  ParsedAttributes DeclAttrs(AttrFactory);
  // Optional C++11 attribute-specifier
  MaybeParseCXX11Attributes(DeclAttrs);

  // The next token may be an OpenMP pragma annotation token. That would
  // normally be handled from ParseCXXClassMemberDeclarationWithPragmas, but in
  // this case, it came from an *attribute* rather than a pragma. Handle it now.
  if (Tok.is(tok::annot_attr_openmp))
    return ParseOpenMPDeclarativeDirectiveWithExtDecl(AS, DeclAttrs);

  ParsedAttributes DeclSpecAttrs(AttrFactory);
  MaybeParseMicrosoftAttributes(DeclSpecAttrs);

  // Hold late-parsed attributes so we can attach a Decl to them later.
  LateParsedAttrList CommonLateParsedAttrs;

  // decl-specifier-seq:
  // Parse the common declaration-specifiers piece.
  ParsingDeclSpec DS(*this, TemplateDiags);
  DS.takeAttributesFrom(DeclSpecAttrs);

  if (MalformedTypeSpec)
    DS.SetTypeSpecError();

  // Turn off usual access checking for templates explicit specialization
  // and instantiation.
  // C++20 [temp.spec] 13.9/6.
  // This disables the access checking rules for member function template
  // explicit instantiation and explicit specialization.
  bool IsTemplateSpecOrInst =
      (TemplateInfo.Kind == ParsedTemplateInfo::ExplicitInstantiation ||
       TemplateInfo.Kind == ParsedTemplateInfo::ExplicitSpecialization);
  SuppressAccessChecks diagsFromTag(*this, IsTemplateSpecOrInst);

  ParseDeclarationSpecifiers(DS, TemplateInfo, AS, DeclSpecContext::DSC_class,
                             &CommonLateParsedAttrs);

  // Issue diagnostic and remove `typedef` if present.
  if (DS.getStorageClassSpec() == DeclSpec::SCS_typedef &&
      DS.getStorageClassSpecLoc().isValid()) {
    Diag(DS.getStorageClassSpecLoc(), diag::err_typename_invalid_storageclass);
    DS.ClearStorageClassSpecs();
  }

  if (IsTemplateSpecOrInst)
    diagsFromTag.done();

  // Turn off colon protection that was set for declspec.
  X.restore();

  // If we had a free-standing type definition with a missing semicolon, we
  // may get this far before the problem becomes obvious.
  if (DS.hasTagDefinition() &&
      TemplateInfo.Kind == ParsedTemplateInfo::NonTemplate &&
      DiagnoseMissingSemiAfterTagDefinition(DS, AS, DeclSpecContext::DSC_class,
                                            &CommonLateParsedAttrs))
    return nullptr;

  MultiTemplateParamsArg TemplateParams(
      TemplateInfo.TemplateParams ? TemplateInfo.TemplateParams->data()
                                  : nullptr,
      TemplateInfo.TemplateParams ? TemplateInfo.TemplateParams->size() : 0);

  if (TryConsumeToken(tok::semi)) {
    if (DS.isFriendSpecified())
      ProhibitAttributes(DeclAttrs);

    RecordDecl *AnonRecord = nullptr;
    Decl *TheDecl = Actions.ParsedFreeStandingDeclSpec(
        getCurScope(), AS, DS, DeclAttrs, TemplateParams, false, AnonRecord);
    DS.complete(TheDecl);
    if (AnonRecord) {
      Decl *decls[] = {AnonRecord, TheDecl};
      return Actions.BuildDeclaratorGroup(decls);
    }
    return Actions.ConvertDeclToDeclGroup(TheDecl);
  }

  ParsingDeclarator DeclaratorInfo(*this, DS, DeclAttrs,
                                   DeclaratorContext::Member);
  if (TemplateInfo.TemplateParams)
    DeclaratorInfo.setTemplateParameterLists(TemplateParams);

  // Hold late-parsed attributes so we can attach a Decl to them later.
  LateParsedAttrList LateParsedAttrs;

  SmallVector<Decl *, 8> DeclsInGroup;
  ExprResult BitfieldSize;
  bool ExpectSemi = true;

  // Parse the first declarator.
  if (ParseBSCMemberDeclaratorBeforeInitializer(DeclaratorInfo, BitfieldSize,
                                                LateParsedAttrs)) {
    TryConsumeToken(tok::semi);
    return nullptr;
  }

  // Check for a member function definition.
  if (BitfieldSize.isUnset()) {
    FunctionDefinitionKind DefinitionKind = FunctionDefinitionKind::Declaration;
    // function-definition:
    //
    // In C++11, a non-function declarator followed by an open brace is a
    // braced-init-list for an in-class member initialization, not an
    // erroneous function definition.
    if (Tok.is(tok::l_brace) && !getLangOpts().CPlusPlus11) {
      DefinitionKind = FunctionDefinitionKind::Definition;
    } else if (DeclaratorInfo.isFunctionDeclarator()) {
      if (Tok.isOneOf(tok::l_brace, tok::colon, tok::kw_try)) {
        DefinitionKind = FunctionDefinitionKind::Definition;
      }
    }
    DeclaratorInfo.setFunctionDefinitionKind(DefinitionKind);

    if (DefinitionKind != FunctionDefinitionKind::Declaration) {
      if (!DeclaratorInfo.isFunctionDeclarator()) {
        Diag(DeclaratorInfo.getIdentifierLoc(), diag::err_func_def_no_params);
        ConsumeBrace();
        SkipUntil(tok::r_brace);

        // Consume the optional ';'
        TryConsumeToken(tok::semi);

        return nullptr;
      }

      if (DS.getStorageClassSpec() == DeclSpec::SCS_typedef) {
        Diag(DeclaratorInfo.getIdentifierLoc(),
             diag::err_function_declared_typedef);

        // Recover by treating the 'typedef' as spurious.
        DS.ClearStorageClassSpecs();
      }

      Decl *FunDecl = ParseBSCInlineMethodDef(AS, AccessAttrs, DeclaratorInfo,
                                              TemplateInfo);

      if (FunDecl) {
        for (unsigned i = 0, ni = CommonLateParsedAttrs.size(); i < ni; ++i) {
          CommonLateParsedAttrs[i]->addDecl(FunDecl);
        }
        for (unsigned i = 0, ni = LateParsedAttrs.size(); i < ni; ++i) {
          LateParsedAttrs[i]->addDecl(FunDecl);
        }
      }
      LateParsedAttrs.clear();

      // Consume the ';' - it's optional unless we have a delete or default
      if (Tok.is(tok::semi))
        ConsumeExtraSemi(AfterMemberFunctionDefinition);

      return DeclGroupPtrTy::make(DeclGroupRef(FunDecl));
    }
  }

  // member-declarator-list:
  //   member-declarator
  //   member-declarator-list ',' member-declarator

  while (true) {
    // NOTE: If Sema is the Action module and declarator is an instance field,
    // this call will *not* return the created decl; It will return null.
    // See Sema::ActOnCXXMemberDeclarator for details.

    NamedDecl *ThisDecl = nullptr;

    ThisDecl = Actions.ActOnBSCMemberDeclarator(
        getCurScope(), AS, DeclaratorInfo, TemplateParams, BitfieldSize.get());
    if (VarTemplateDecl *VT =
            ThisDecl ? dyn_cast<VarTemplateDecl>(ThisDecl) : nullptr)
      // Re-direct this decl to refer to the templated decl so that we can
      // initialize it.
      ThisDecl = VT->getTemplatedDecl();

    if (ThisDecl)
      Actions.ProcessDeclAttributeList(getCurScope(), ThisDecl, AccessAttrs);

    if (ThisDecl) {
      if (!ThisDecl->isInvalidDecl()) {
        // Set the Decl for any late parsed attributes
        for (unsigned i = 0, ni = CommonLateParsedAttrs.size(); i < ni; ++i)
          CommonLateParsedAttrs[i]->addDecl(ThisDecl);

        for (unsigned i = 0, ni = LateParsedAttrs.size(); i < ni; ++i)
          LateParsedAttrs[i]->addDecl(ThisDecl);
      }
      Actions.FinalizeDeclaration(ThisDecl);
      DeclsInGroup.push_back(ThisDecl);

      if (DeclaratorInfo.isFunctionDeclarator() &&
          DeclaratorInfo.getDeclSpec().getStorageClassSpec() !=
              DeclSpec::SCS_typedef)
        HandleMemberFunctionDeclDelays(DeclaratorInfo, ThisDecl);
    }
    LateParsedAttrs.clear();

    DeclaratorInfo.complete(ThisDecl);

    // If we don't have a comma, it is either the end of the list (a ';')
    // or an error, bail out.
    SourceLocation CommaLoc;
    if (!TryConsumeToken(tok::comma, CommaLoc)) {
      if (getLangOpts().BSC && ThisDecl->getAsFunction()) {
        if (BSCMethodDecl *BSCMD =
                dyn_cast<BSCMethodDecl>(ThisDecl->getAsFunction())) {
          if (BSCMD->isDestructor() && !ThisDecl->isInvalidDecl()) {
            Actions.CheckBSCDestructorBody(
                dyn_cast<FunctionDecl>(ThisDecl->getAsFunction()));
          }
        }
      }
      break;
    }

    if (Tok.isAtStartOfLine() &&
        !MightBeDeclarator(DeclaratorContext::Member)) {
      // This comma was followed by a line-break and something which can't be
      // the start of a declarator. The comma was probably a typo for a
      // semicolon.
      Diag(CommaLoc, diag::err_expected_semi_declaration)
          << FixItHint::CreateReplacement(CommaLoc, ";");
      ExpectSemi = false;
      break;
    }

    // Parse the next declarator.
    DeclaratorInfo.clear();
    BitfieldSize = ExprResult(/*Invalid=*/false);
    DeclaratorInfo.setCommaLoc(CommaLoc);

    // GNU attributes are allowed before the second and subsequent declarator.
    // However, this does not apply for [[]] attributes (which could show up
    // before or after the __attribute__ attributes).
    DiagnoseAndSkipCXX11Attributes();
    MaybeParseGNUAttributes(DeclaratorInfo);
    DiagnoseAndSkipCXX11Attributes();

    if (ParseBSCMemberDeclaratorBeforeInitializer(DeclaratorInfo, BitfieldSize,
                                                  LateParsedAttrs))
      break;
  }

  if (ExpectSemi &&
      ExpectAndConsume(tok::semi, diag::err_expected_semi_decl_list)) {
    // Skip to end of block or statement.
    SkipUntil(tok::r_brace, StopAtSemi | StopBeforeMatch);
    // If we stopped at a ';', eat it.
    TryConsumeToken(tok::semi);
    return nullptr;
  }

  return Actions.FinalizeDeclaratorGroup(getCurScope(), DS, DeclsInGroup);
}

bool Parser::ParseBSCMemberDeclaratorBeforeInitializer(
    Declarator &DeclaratorInfo, ExprResult &BitfieldSize,
    LateParsedAttrList &LateParsedAttrs) {
  // member-declarator:
  //   declarator requires-clause
  //   declarator brace-or-equal-initializer[opt]
  //   identifier attribute-specifier-seq[opt] ':' constant-expression
  //       brace-or-equal-initializer[opt]
  //   ':' constant-expression
  //
  // NOTE: the latter two productions are a proposed bugfix rather than the
  // current grammar rules as of C++20.
  if (Tok.isNot(tok::colon))
    ParseDeclarator(DeclaratorInfo);
  else
    DeclaratorInfo.SetIdentifier(nullptr, Tok.getLocation());

  if (!DeclaratorInfo.isFunctionDeclarator() && TryConsumeToken(tok::colon)) {
    assert(DeclaratorInfo.isPastIdentifier() &&
           "don't know where identifier would go yet?");
    BitfieldSize = ParseConstantExpression();
    if (BitfieldSize.isInvalid())
      SkipUntil(tok::comma, StopAtSemi | StopBeforeMatch);
  } else {
  }

  // If a simple-asm-expr is present, parse it.
  if (Tok.is(tok::kw_asm)) {
    SourceLocation Loc;
    ExprResult AsmLabel(ParseSimpleAsm(/*ForAsmLabel*/ true, &Loc));
    if (AsmLabel.isInvalid())
      SkipUntil(tok::comma, StopAtSemi | StopBeforeMatch);

    DeclaratorInfo.setAsmLabel(AsmLabel.get());
    DeclaratorInfo.SetRangeEnd(Loc);
  }

  // If attributes exist after the declarator, but before an '{', parse them.
  // However, this does not apply for [[]] attributes (which could show up
  // before or after the __attribute__ attributes).
  DiagnoseAndSkipCXX11Attributes();
  MaybeParseGNUAttributes(DeclaratorInfo, &LateParsedAttrs);
  DiagnoseAndSkipCXX11Attributes();

  // If this has neither a name nor a bit width, something has gone seriously
  // wrong. Skip until the semi-colon or }.
  if (!DeclaratorInfo.hasName() && BitfieldSize.isUnset()) {
    // If so, skip until the semi-colon or a }.
    SkipUntil(tok::r_brace, StopAtSemi | StopBeforeMatch);
    return true;
  }
  return false;
}

// The extended type of a BSC member function cannot be a generic typealias, for example:
//     typedef MyS<T> = struct S<T>;
//     void MyS<T>::foo(This* this);
bool Parser::ExtendedTypeOfBSCMemberFunctionIsTypealias(DeclSpec &DS) {
  IdentifierInfo *CurName = Tok.getIdentifierInfo();
  SourceLocation CurNameLoc = Tok.getLocation();
  LookupResult LookupPreviousTypealias(Actions, CurName, CurNameLoc,
                                        Sema::LookupOrdinaryName,
                                        Sema::NotForRedeclaration);
  Actions.LookupName(LookupPreviousTypealias, getCurScope());
  if (LookupPreviousTypealias.isSingleResult()) {
    TypeAliasTemplateDecl *TATD = dyn_cast_or_null<TypeAliasTemplateDecl>(LookupPreviousTypealias.getFoundDecl());
    if (TATD) {
      Diag(CurNameLoc, diag::err_extended_type_not_generic_typealias);
      DS.SetTypeSpecError();
      SkipUntil(tok::coloncolon);
      return true;
    }
  }
  return false;
}

/// The BSC conditional specifier allows for conditional type based on a constant expression, as follows:
///           __conditional ( constant expression, type-name, type-name )
void Parser::ParseConditionalSpecifier(DeclSpec &DS) {
  assert(Tok.is(tok::kw___conditional) && "Not a conditional specifier");
  SourceLocation KWLoc = ConsumeToken();  // Consume __conditional

  BalancedDelimiterTracker T(*this, tok::l_paren);
  if (T.expectAndConsume())
    return;

  Sema::ConditionResult Cond;
  llvm::Optional<bool> CondResult;
  ExprResult CondExpr = ParseExpression();
  if (CondExpr.isInvalid()) {
    Cond = Sema::ConditionError();
    T.skipToEnd();
    return;
  } else
    Cond = Actions.ActOnCondition(getCurScope(), KWLoc, CondExpr.get(),
                                  Sema::ConditionKind::ConstexprIf,
                                  /*MissingOK=*/false);
  if (Cond.isInvalid() || Tok.isNot(tok::comma)) {
    T.skipToEnd();
    return;
  }
  CondResult = Cond.getKnownValue();
  ConsumeToken(); // Consume comma

  // Parse the next two types.
  TypeResult Ty1 = ParseTypeName();
  if (ExpectAndConsume(tok::comma)) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return;
  }
  TypeResult Ty2 = ParseTypeName();
  if (Ty1.isInvalid() || Ty2.isInvalid()) {
      T.skipToEnd();
      return;
  }
  // Closing ')'.
  if (T.consumeClose())
    return;
  DS.setTypeofParensRange(T.getRange());
  ParsedType PT1 = Ty1.get();
  ParsedType PT2 = Ty2.get();
  const char *PrevSpec = nullptr;
  unsigned DiagID;
  if (DS.SetConditionalType(KWLoc, PrevSpec, DiagID,
                            CondResult, CondExpr.get(), PT1, PT2,
                            Actions.getASTContext().getPrintingPolicy()))
    Diag(KWLoc, DiagID) << PrevSpec;
}

bool DeclSpec::SetConditionalType(SourceLocation KWLoc,
                                  const char *&PrevSpec, unsigned &DiagID,
                                  llvm::Optional<bool> CondResult,
                                  Expr *CondExpr, ParsedType Ty1, ParsedType Ty2,
                                  const PrintingPolicy &Policy) {
  if (TypeSpecType == TST_error)
    return false;
  if (TypeSpecType != TST_unspecified) {
    PrevSpec = DeclSpec::getSpecifierName((TST) TypeSpecType, Policy);
    DiagID = diag::err_invalid_decl_spec_combination;
    return true;
  }

  TypeSpecType = TST_conditionalType;
  TSTLoc = KWLoc;
  TSTNameLoc = KWLoc;
  TypeSpecOwned = false;

  ConditionalCondResult = CondResult;
  ConditionalCondExpr = CondExpr;
  ConditionalType1 = Ty1;
  ConditionalType2 = Ty2;
  return false;
}

/// [BSC] HandleBSCUnknownTypeName - This method is called when we have an non-typename
/// identifier in a declspec (which normally terminates the decl spec).
/// In this case, the declspec is malformed. For example:
///      typedef long long int LLInt;
///      struct Array<LLint B> {};
bool Parser::HandleBSCUnknownTypeName(DeclSpec &DS, Token Tok) {
  SourceLocation Loc = Tok.getLocation();
  // This is almost certainly an invalid type name. Let Sema emit a diagnostic
  // and attempt to recover.
  ParsedType T;
  IdentifierInfo *II = Tok.getIdentifierInfo();
  Actions.DiagnoseUnknownTypeName(II, Loc, getCurScope(), nullptr, T, false);
  if (T) {
    // The action has suggested that the type T could be used. Set that as
    // the type in the declaration specifiers, consume the would-be type
    // name token, and we're done.
    const char *PrevSpec;
    unsigned DiagID;
    DS.SetTypeSpecType(DeclSpec::TST_typename, Loc, PrevSpec, DiagID, T,
                      Actions.getASTContext().getPrintingPolicy());
    DS.SetRangeEnd(Tok.getLocation());
    BSCGenericLookAhead++;
    return true;
    // There may be other declaration specifiers after this.
  } else if (II != Tok.getIdentifierInfo()) {
    // If no type was suggested, the correction is to a keyword
    Tok.setKind(II->getTokenID());
    // There may be other declaration specifiers after this.
    BSCGenericLookAhead++;
    return true;
  }

  // Otherwise, the action had no suggestion for us.  Mark this as an error.
  DS.SetTypeSpecError();
  DS.SetRangeEnd(Tok.getLocation());
  BSCGenericLookAhead++;
  return true;
}
#endif
