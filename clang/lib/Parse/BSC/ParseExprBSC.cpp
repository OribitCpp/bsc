//===--- ParseExprBSC.cpp - BSC Expression Parsing ------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the Expression parsing implementation for BSC.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/Parse/Parser.h"
#include "clang/AST/ASTContext.h"
#include "clang/Parse/RAIIObjectsForParser.h"

using namespace clang;

ExprResult Parser::ParseOptionalBSCScopeSpecifier(
    CastParseKind ParseKind, bool isAddressOfOperand, bool &NotCastExpr,
    TypeCastState isTypeCast, bool isVectorLiteral, bool *NotPrimaryExpression,
    bool HasBSCScopeSpec) {
  CXXScopeSpec SS;
  if (Tok.is(tok::annot_template_id) && NextToken().is(tok::coloncolon)) {
    TemplateIdAnnotation *TemplateId = takeTemplateIdAnnotation(Tok);
    SourceLocation CCLoc = NextToken().getLocation();
    ASTTemplateArgsPtr TemplateArgsPtr(TemplateId->getTemplateArgs(),
                                        TemplateId->NumArgs);
    Actions.ActOnCXXNestedNameSpecifier(
        getCurScope(), SS, TemplateId->TemplateKWLoc, TemplateId->Template,
        TemplateId->TemplateNameLoc, TemplateId->LAngleLoc, TemplateArgsPtr,
        TemplateId->RAngleLoc, CCLoc, /*EnteringContext*/ false);
  }
  ParsingDeclSpec DS(*this);
  ParseBSCScopeSpecifiers(DS);
  ParsedAttributes EmptyDeclSpecAttrs(AttrFactory);
  ParsingDeclarator D(*this, DS, EmptyDeclSpecAttrs, DeclaratorContext::File);

  BSCScopeSpec BSS;
  BSS.setBeginLoc(DS.getBeginLoc());
  QualType T =
      Actions.ConvertBSCScopeSpecToType(D, DS.getBeginLoc(), false, BSS, DS);
  // For generic member functions, if the generic 'T' comes from a scope when
  // called, we need to obtain the NestedNameSpecifier from the scope and store
  // it in QualType to facilitate the creation of 'DependentScopeDeclRefExpr'
  // ast nodes.
  auto *TST = dyn_cast_or_null<TemplateSpecializationType>(T.getCanonicalType().getTypePtr());
  if (Tok.is(tok::coloncolon) && TST) {
    TagDecl *TD = dyn_cast_or_null<TagDecl>(Actions.getASTContext().BSCDeclContextMap[TST]);
    if (TD)
      TD->setQualifierInfo(SS.getWithLocInContext(Actions.getASTContext()));
  }
  HasBSCScopeSpec = TryConsumeToken(tok::coloncolon);
  D.getBSCScopeSpec() = BSS;

  if (Tok.isNot(tok::identifier)) {
    Diag(Tok, diag::err_expected_unqualified_id) << 0;
    return ExprError();
  }
  return ParseCastExpression(ParseKind, isAddressOfOperand, NotCastExpr,
                             isTypeCast, isVectorLiteral, NotPrimaryExpression,
                             T, HasBSCScopeSpec, DS.getBeginLoc()
#if ENABLE_BSC
                             ,
                             SS
#endif
  );
}

bool Parser::IsBSCStaticMemberFunctionCallInTemplateArgumentList() {
  int LessCount = 0;
  int i = 0;
  Token CurrTok = Tok;
  Token NextTok = PP.LookAhead(i);
  while (!NextTok.isOneOf(tok::semi, tok::l_brace, tok::eof, tok::equal)) {
    if (CurrTok.is(tok::less))
      LessCount++;
    if (CurrTok.is(tok::greater))
      LessCount--;
    if (CurrTok.is(tok::greatergreater))
      LessCount = LessCount - 2;
    if (LessCount < 0) return false;
    if (!LessCount) {
      if (CurrTok.is(tok::coloncolon))
        return true;
      if (NextTok.isOneOf(tok::comma, tok::greater))
        return false;
    }
    CurrTok = NextTok;
    NextTok = PP.LookAhead(++i);
  }
  return false;
}

bool Parser::IsBSCStaticMemberFunctionCall() {
  assert(Tok.isOneOf(tok::identifier, tok::kw_union, tok::kw_enum, tok::kw_struct));
  Token NextTok = Tok.is(tok::identifier) ? PP.LookAhead(0) : PP.LookAhead(1);
  if (NextTok.is(tok::coloncolon))
    return true;
  if (NextTok.is(tok::less)) {
    if (Tok.isOneOf(tok::kw_struct, tok::kw_union)) {
      ParsedAttributes Attributes(AttrFactory);
      TryParseBSCGenericClassSpecifier(Attributes);
    } else {
      IdentifierInfo &II = *Tok.getIdentifierInfo();
      TemplateTy Template;
      UnqualifiedId TemplateName;
      TemplateName.setIdentifier(&II, Tok.getLocation());
      CXXScopeSpec SS;
      bool MemberOfUnknownSpecialization;
      if (TemplateNameKind TNK =
              Actions.isTemplateName(getCurScope(), SS,
                                     /*hasTemplateKeyword=*/false, TemplateName,
                                     /*ObjectType=*/nullptr,
                                     /*EnteringContext=*/false, Template,
                                     MemberOfUnknownSpecialization)) {
        if (TNK == TNK_Type_template) {
          ConsumeToken();
          if (AnnotateTemplateIdToken(Template, TNK, SS, SourceLocation(),
                                      TemplateName, false))
            return false;
        }
      }
    }
    if (Tok.is(tok::annot_template_id) && NextToken().is(tok::coloncolon))
      return true;
  }
  return false;
}

bool Parser::IsSupportedOverloadType(OverloadedOperatorKind Op) {
  switch (Op) {
  case OO_Plus:
  case OO_Minus:
  case OO_Star:
  case OO_Slash:
  case OO_Percent:
  case OO_Caret:
  case OO_Amp:
  case OO_Pipe:
  case OO_Tilde:
  case OO_LessLess:
  case OO_GreaterGreater:
  case OO_Less:
  case OO_LessEqual:
  case OO_Greater:
  case OO_GreaterEqual:
  case OO_EqualEqual:
  case OO_ExclaimEqual:
  case OO_Arrow:
  case OO_Subscript:
    return true;
  default:
    return false;
  }
}

#endif // ENABLE_BSC