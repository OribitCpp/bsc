//===--- ParseTentative.cpp - Ambiguity Resolution Parsing ----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file implements the tentative parsing portions of the Parser
//  interfaces, for ambiguity resolution.
//
//===----------------------------------------------------------------------===//

#include "clang/Parse/Parser.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Sema/ParsedTemplate.h"
#include "clang/Sema/Lookup.h"
using namespace clang;

/// isCXXDeclarationStatement - C++-specialized function that disambiguates
/// between a declaration or an expression statement, when parsing function
/// bodies. Returns true for declaration, false for expression.
///
///         declaration-statement:
///           block-declaration
///
///         block-declaration:
///           simple-declaration
///           asm-definition
///           namespace-alias-definition
///           using-declaration
///           using-directive
/// [C++0x]   static_assert-declaration
///
///         asm-definition:
///           'asm' '(' string-literal ')' ';'
///
///         namespace-alias-definition:
///           'namespace' identifier = qualified-namespace-specifier ';'
///
///         using-declaration:
///           'using' typename[opt] '::'[opt] nested-name-specifier
///                 unqualified-id ';'
///           'using' '::' unqualified-id ;
///
///         using-directive:
///           'using' 'namespace' '::'[opt] nested-name-specifier[opt]
///                 namespace-name ';'
///
bool Parser::isCXXDeclarationStatement() {
  switch (Tok.getKind()) {
    // asm-definition
  case tok::kw_asm:
    // namespace-alias-definition
  case tok::kw_namespace:
    // using-declaration
    // using-directive
  case tok::kw_using:
    // static_assert-declaration
  case tok::kw_static_assert:
  case tok::kw__Static_assert:
    return true;
    // simple-declaration
  default:
    return isCXXSimpleDeclaration(/*AllowForRangeDecl=*/false);
  }
}

/// isCXXSimpleDeclaration - C++-specialized function that disambiguates
/// between a simple-declaration or an expression-statement.
/// If during the disambiguation process a parsing error is encountered,
/// the function returns true to let the declaration parsing code handle it.
/// Returns false if the statement is disambiguated as expression.
///
/// simple-declaration:
///   decl-specifier-seq init-declarator-list[opt] ';'
///   decl-specifier-seq ref-qualifier[opt] '[' identifier-list ']'
///                      brace-or-equal-initializer ';'    [C++17]
///
/// (if AllowForRangeDecl specified)
/// for ( for-range-declaration : for-range-initializer ) statement
///
/// for-range-declaration:
///    decl-specifier-seq declarator
///    decl-specifier-seq ref-qualifier[opt] '[' identifier-list ']'
///
/// In any of the above cases there can be a preceding attribute-specifier-seq,
/// but the caller is expected to handle that.
bool Parser::isCXXSimpleDeclaration(bool AllowForRangeDecl) {
  // C++ 6.8p1:
  // There is an ambiguity in the grammar involving expression-statements and
  // declarations: An expression-statement with a function-style explicit type
  // conversion (5.2.3) as its leftmost subexpression can be indistinguishable
  // from a declaration where the first declarator starts with a '('. In those
  // cases the statement is a declaration. [Note: To disambiguate, the whole
  // statement might have to be examined to determine if it is an
  // expression-statement or a declaration].

  // C++ 6.8p3:
  // The disambiguation is purely syntactic; that is, the meaning of the names
  // occurring in such a statement, beyond whether they are type-names or not,
  // is not generally used in or changed by the disambiguation. Class
  // templates are instantiated as necessary to determine if a qualified name
  // is a type-name. Disambiguation precedes parsing, and a statement
  // disambiguated as a declaration may be an ill-formed declaration.

  // We don't have to parse all of the decl-specifier-seq part. There's only
  // an ambiguity if the first decl-specifier is
  // simple-type-specifier/typename-specifier followed by a '(', which may
  // indicate a function-style cast expression.
  // isCXXDeclarationSpecifier will return TPResult::Ambiguous only in such
  // a case.

  bool InvalidAsDeclaration = false;
  TPResult TPR = isCXXDeclarationSpecifier(TPResult::False,
                                           &InvalidAsDeclaration);
  if (TPR != TPResult::Ambiguous)
    return TPR != TPResult::False; // Returns true for TPResult::True or
                                   // TPResult::Error.

  // FIXME: TryParseSimpleDeclaration doesn't look past the first initializer,
  // and so gets some cases wrong. We can't carry on if we've already seen
  // something which makes this statement invalid as a declaration in this case,
  // since it can cause us to misparse valid code. Revisit this once
  // TryParseInitDeclaratorList is fixed.
  if (InvalidAsDeclaration)
    return false;

  // FIXME: Add statistics about the number of ambiguous statements encountered
  // and how they were resolved (number of declarations+number of expressions).

  // Ok, we have a simple-type-specifier/typename-specifier followed by a '(',
  // or an identifier which doesn't resolve as anything. We need tentative
  // parsing...

  {
    RevertingTentativeParsingAction PA(*this);
    TPR = TryParseSimpleDeclaration(AllowForRangeDecl);
  }

  // In case of an error, let the declaration parsing code handle it.
  if (TPR == TPResult::Error)
    return true;

  // Declarations take precedence over expressions.
  if (TPR == TPResult::Ambiguous)
    TPR = TPResult::True;

  assert(TPR == TPResult::True || TPR == TPResult::False);
  return TPR == TPResult::True;
}

/// Try to consume a token sequence that we've already identified as
/// (potentially) starting a decl-specifier.
Parser::TPResult Parser::TryConsumeDeclarationSpecifier() {
  switch (Tok.getKind()) {
  case tok::kw__Atomic:
    if (NextToken().isNot(tok::l_paren)) {
      ConsumeToken();
      break;
    }
    LLVM_FALLTHROUGH;
  case tok::kw_typeof:
  case tok::kw___attribute:
  case tok::kw___underlying_type: {
    ConsumeToken();
    if (Tok.isNot(tok::l_paren))
      return TPResult::Error;
    ConsumeParen();
    if (!SkipUntil(tok::r_paren))
      return TPResult::Error;
    break;
  }

  case tok::kw_class:
  case tok::kw_struct:
  case tok::kw_union:
#if ENABLE_BSC
  case tok::kw_trait:
#endif
  case tok::kw___interface:
  case tok::kw_enum:
    // elaborated-type-specifier:
    //     class-key attribute-specifier-seq[opt]
    //         nested-name-specifier[opt] identifier
    //     class-key nested-name-specifier[opt] template[opt] simple-template-id
    //     enum nested-name-specifier[opt] identifier
    //
    // FIXME: We don't support class-specifiers nor enum-specifiers here.
    ConsumeToken();

    // Skip attributes.
    if (!TrySkipAttributes())
      return TPResult::Error;

    if (TryAnnotateOptionalCXXScopeToken())
      return TPResult::Error;
    if (Tok.is(tok::annot_cxxscope))
      ConsumeAnnotationToken();
    if (Tok.is(tok::identifier))
      ConsumeToken();
    else if (Tok.is(tok::annot_template_id))
      ConsumeAnnotationToken();
    else
      return TPResult::Error;
    break;

  case tok::annot_cxxscope:
    ConsumeAnnotationToken();
    LLVM_FALLTHROUGH;
  default:
    ConsumeAnyToken();

    if (getLangOpts().ObjC && Tok.is(tok::less))
      return TryParseProtocolQualifiers();
    break;
  }

  return TPResult::Ambiguous;
}

/// simple-declaration:
///   decl-specifier-seq init-declarator-list[opt] ';'
///
/// (if AllowForRangeDecl specified)
/// for ( for-range-declaration : for-range-initializer ) statement
/// for-range-declaration:
///    attribute-specifier-seqopt type-specifier-seq declarator
///
Parser::TPResult Parser::TryParseSimpleDeclaration(bool AllowForRangeDecl) {
  if (TryConsumeDeclarationSpecifier() == TPResult::Error)
    return TPResult::Error;

  // Two decl-specifiers in a row conclusively disambiguate this as being a
  // simple-declaration. Don't bother calling isCXXDeclarationSpecifier in the
  // overwhelmingly common case that the next token is a '('.
  if (Tok.isNot(tok::l_paren)) {
    TPResult TPR = isCXXDeclarationSpecifier();
    if (TPR == TPResult::Ambiguous)
      return TPResult::True;
    if (TPR == TPResult::True || TPR == TPResult::Error)
      return TPR;
    assert(TPR == TPResult::False);
  }

  TPResult TPR = TryParseInitDeclaratorList();
  if (TPR != TPResult::Ambiguous)
    return TPR;

  if (Tok.isNot(tok::semi) && (!AllowForRangeDecl || Tok.isNot(tok::colon)))
    return TPResult::False;

  return TPResult::Ambiguous;
}

/// Tentatively parse an init-declarator-list in order to disambiguate it from
/// an expression.
///
///       init-declarator-list:
///         init-declarator
///         init-declarator-list ',' init-declarator
///
///       init-declarator:
///         declarator initializer[opt]
/// [GNU]   declarator simple-asm-expr[opt] attributes[opt] initializer[opt]
///
///       initializer:
///         brace-or-equal-initializer
///         '(' expression-list ')'
///
///       brace-or-equal-initializer:
///         '=' initializer-clause
/// [C++11] braced-init-list
///
///       initializer-clause:
///         assignment-expression
///         braced-init-list
///
///       braced-init-list:
///         '{' initializer-list ','[opt] '}'
///         '{' '}'
///
Parser::TPResult Parser::TryParseInitDeclaratorList() {
  while (true) {
    // declarator
    TPResult TPR = TryParseDeclarator(false/*mayBeAbstract*/);
    if (TPR != TPResult::Ambiguous)
      return TPR;

    // [GNU] simple-asm-expr[opt] attributes[opt]
    if (Tok.isOneOf(tok::kw_asm, tok::kw___attribute))
      return TPResult::True;

    // initializer[opt]
    if (Tok.is(tok::l_paren)) {
      // Parse through the parens.
      ConsumeParen();
      if (!SkipUntil(tok::r_paren, StopAtSemi))
        return TPResult::Error;
    } else if (Tok.is(tok::l_brace)) {
      // A left-brace here is sufficient to disambiguate the parse; an
      // expression can never be followed directly by a braced-init-list.
      return TPResult::True;
    } else if (Tok.is(tok::equal) || isTokIdentifier_in()) {
      // MSVC and g++ won't examine the rest of declarators if '=' is
      // encountered; they just conclude that we have a declaration.
      // EDG parses the initializer completely, which is the proper behavior
      // for this case.
      //
      // At present, Clang follows MSVC and g++, since the parser does not have
      // the ability to parse an expression fully without recording the
      // results of that parse.
      // FIXME: Handle this case correctly.
      //
      // Also allow 'in' after an Objective-C declaration as in:
      // for (int (^b)(void) in array). Ideally this should be done in the
      // context of parsing for-init-statement of a foreach statement only. But,
      // in any other context 'in' is invalid after a declaration and parser
      // issues the error regardless of outcome of this decision.
      // FIXME: Change if above assumption does not hold.
      return TPResult::True;
    }

    if (!TryConsumeToken(tok::comma))
      break;
  }

  return TPResult::Ambiguous;
}

struct Parser::ConditionDeclarationOrInitStatementState {
  Parser &P;
  bool CanBeExpression = true;
  bool CanBeCondition = true;
  bool CanBeInitStatement;
  bool CanBeForRangeDecl;

  ConditionDeclarationOrInitStatementState(Parser &P, bool CanBeInitStatement,
                                           bool CanBeForRangeDecl)
      : P(P), CanBeInitStatement(CanBeInitStatement),
        CanBeForRangeDecl(CanBeForRangeDecl) {}

  bool resolved() {
    return CanBeExpression + CanBeCondition + CanBeInitStatement +
               CanBeForRangeDecl < 2;
  }

  void markNotExpression() {
    CanBeExpression = false;

    if (!resolved()) {
      // FIXME: Unify the parsing codepaths for condition variables and
      // simple-declarations so that we don't need to eagerly figure out which
      // kind we have here. (Just parse init-declarators until we reach a
      // semicolon or right paren.)
      RevertingTentativeParsingAction PA(P);
      if (CanBeForRangeDecl) {
        // Skip until we hit a ')', ';', or a ':' with no matching '?'.
        // The final case is a for range declaration, the rest are not.
        unsigned QuestionColonDepth = 0;
        while (true) {
          P.SkipUntil({tok::r_paren, tok::semi, tok::question, tok::colon},
                      StopBeforeMatch);
          if (P.Tok.is(tok::question))
            ++QuestionColonDepth;
          else if (P.Tok.is(tok::colon)) {
            if (QuestionColonDepth)
              --QuestionColonDepth;
            else {
              CanBeCondition = CanBeInitStatement = false;
              return;
            }
          } else {
            CanBeForRangeDecl = false;
            break;
          }
          P.ConsumeToken();
        }
      } else {
        // Just skip until we hit a ')' or ';'.
        P.SkipUntil(tok::r_paren, tok::semi, StopBeforeMatch);
      }
      if (P.Tok.isNot(tok::r_paren))
        CanBeCondition = CanBeForRangeDecl = false;
      if (P.Tok.isNot(tok::semi))
        CanBeInitStatement = false;
    }
  }

  bool markNotCondition() {
    CanBeCondition = false;
    return resolved();
  }

  bool markNotForRangeDecl() {
    CanBeForRangeDecl = false;
    return resolved();
  }

  bool update(TPResult IsDecl) {
    switch (IsDecl) {
    case TPResult::True:
      markNotExpression();
      assert(resolved() && "can't continue after tentative parsing bails out");
      break;
    case TPResult::False:
      CanBeCondition = CanBeInitStatement = CanBeForRangeDecl = false;
      break;
    case TPResult::Ambiguous:
      break;
    case TPResult::Error:
      CanBeExpression = CanBeCondition = CanBeInitStatement =
          CanBeForRangeDecl = false;
      break;
    }
    return resolved();
  }

  ConditionOrInitStatement result() const {
    assert(CanBeExpression + CanBeCondition + CanBeInitStatement +
                   CanBeForRangeDecl < 2 &&
           "result called but not yet resolved");
    if (CanBeExpression)
      return ConditionOrInitStatement::Expression;
    if (CanBeCondition)
      return ConditionOrInitStatement::ConditionDecl;
    if (CanBeInitStatement)
      return ConditionOrInitStatement::InitStmtDecl;
    if (CanBeForRangeDecl)
      return ConditionOrInitStatement::ForRangeDecl;
    return ConditionOrInitStatement::Error;
  }
};

bool Parser::isEnumBase(bool AllowSemi) {
  assert(Tok.is(tok::colon) && "should be looking at the ':'");

  RevertingTentativeParsingAction PA(*this);
  // ':'
  ConsumeToken();

  // type-specifier-seq
  bool InvalidAsDeclSpec = false;
  // FIXME: We could disallow non-type decl-specifiers here, but it makes no
  // difference: those specifiers are ill-formed regardless of the
  // interpretation.
  TPResult R = isCXXDeclarationSpecifier(/*BracedCastResult*/ TPResult::True,
                                         &InvalidAsDeclSpec);
  if (R == TPResult::Ambiguous) {
    // We either have a decl-specifier followed by '(' or an undeclared
    // identifier.
    if (TryConsumeDeclarationSpecifier() == TPResult::Error)
      return true;

    // If we get to the end of the enum-base, we hit either a '{' or a ';'.
    // Don't bother checking the enumerator-list.
    if (Tok.is(tok::l_brace) || (AllowSemi && Tok.is(tok::semi)))
      return true;

    // A second decl-specifier unambiguously indicatges an enum-base.
    R = isCXXDeclarationSpecifier(TPResult::True, &InvalidAsDeclSpec);
  }

  return R != TPResult::False;
}

/// Disambiguates between a declaration in a condition, a
/// simple-declaration in an init-statement, and an expression for
/// a condition of a if/switch statement.
///
///       condition:
///         expression
///         type-specifier-seq declarator '=' assignment-expression
/// [C++11] type-specifier-seq declarator '=' initializer-clause
/// [C++11] type-specifier-seq declarator braced-init-list
/// [GNU]   type-specifier-seq declarator simple-asm-expr[opt] attributes[opt]
///             '=' assignment-expression
///       simple-declaration:
///         decl-specifier-seq init-declarator-list[opt] ';'
///
/// Note that, unlike isCXXSimpleDeclaration, we must disambiguate all the way
/// to the ';' to disambiguate cases like 'int(x))' (an expression) from
/// 'int(x);' (a simple-declaration in an init-statement).
Parser::ConditionOrInitStatement
Parser::isCXXConditionDeclarationOrInitStatement(bool CanBeInitStatement,
                                                 bool CanBeForRangeDecl) {
  ConditionDeclarationOrInitStatementState State(*this, CanBeInitStatement,
                                                 CanBeForRangeDecl);

  if (CanBeInitStatement && Tok.is(tok::kw_using))
    return ConditionOrInitStatement::InitStmtDecl;
  if (State.update(isCXXDeclarationSpecifier()))
    return State.result();

  // It might be a declaration; we need tentative parsing.
  RevertingTentativeParsingAction PA(*this);

  // FIXME: A tag definition unambiguously tells us this is an init-statement.
  if (State.update(TryConsumeDeclarationSpecifier()))
    return State.result();
  assert(Tok.is(tok::l_paren) && "Expected '('");

  while (true) {
    // Consume a declarator.
    if (State.update(TryParseDeclarator(false/*mayBeAbstract*/)))
      return State.result();

    // Attributes, asm label, or an initializer imply this is not an expression.
    // FIXME: Disambiguate properly after an = instead of assuming that it's a
    // valid declaration.
    if (Tok.isOneOf(tok::equal, tok::kw_asm, tok::kw___attribute) ||
        (getLangOpts().CPlusPlus11 && Tok.is(tok::l_brace))) {
      State.markNotExpression();
      return State.result();
    }

    // A colon here identifies a for-range declaration.
    if (State.CanBeForRangeDecl && Tok.is(tok::colon))
      return ConditionOrInitStatement::ForRangeDecl;

    // At this point, it can't be a condition any more, because a condition
    // must have a brace-or-equal-initializer.
    if (State.markNotCondition())
      return State.result();

    // Likewise, it can't be a for-range declaration any more.
    if (State.markNotForRangeDecl())
      return State.result();

    // A parenthesized initializer could be part of an expression or a
    // simple-declaration.
    if (Tok.is(tok::l_paren)) {
      ConsumeParen();
      SkipUntil(tok::r_paren, StopAtSemi);
    }

    if (!TryConsumeToken(tok::comma))
      break;
  }

  // We reached the end. If it can now be some kind of decl, then it is.
  if (State.CanBeCondition && Tok.is(tok::r_paren))
    return ConditionOrInitStatement::ConditionDecl;
  else if (State.CanBeInitStatement && Tok.is(tok::semi))
    return ConditionOrInitStatement::InitStmtDecl;
  else
    return ConditionOrInitStatement::Expression;
}

  /// Determine whether the next set of tokens contains a type-id.
  ///
  /// The context parameter states what context we're parsing right
  /// now, which affects how this routine copes with the token
  /// following the type-id. If the context is TypeIdInParens, we have
  /// already parsed the '(' and we will cease lookahead when we hit
  /// the corresponding ')'. If the context is
  /// TypeIdAsTemplateArgument, we've already parsed the '<' or ','
  /// before this template argument, and will cease lookahead when we
  /// hit a '>', '>>' (in C++0x), or ','; or, in C++0x, an ellipsis immediately
  /// preceding such. Returns true for a type-id and false for an expression.
  /// If during the disambiguation process a parsing error is encountered,
  /// the function returns true to let the declaration parsing code handle it.
  ///
  /// type-id:
  ///   type-specifier-seq abstract-declarator[opt]
  ///
bool Parser::isCXXTypeId(TentativeCXXTypeIdContext Context, bool &isAmbiguous) {

  isAmbiguous = false;

  // C++ 8.2p2:
  // The ambiguity arising from the similarity between a function-style cast and
  // a type-id can occur in different contexts. The ambiguity appears as a
  // choice between a function-style cast expression and a declaration of a
  // type. The resolution is that any construct that could possibly be a type-id
  // in its syntactic context shall be considered a type-id.

  TPResult TPR = isCXXDeclarationSpecifier();
  if (TPR != TPResult::Ambiguous)
    return TPR != TPResult::False; // Returns true for TPResult::True or
                                     // TPResult::Error.

  // FIXME: Add statistics about the number of ambiguous statements encountered
  // and how they were resolved (number of declarations+number of expressions).

  // Ok, we have a simple-type-specifier/typename-specifier followed by a '('.
  // We need tentative parsing...

  RevertingTentativeParsingAction PA(*this);

  // type-specifier-seq
  TryConsumeDeclarationSpecifier();
  assert(Tok.is(tok::l_paren) && "Expected '('");

  // declarator
  TPR = TryParseDeclarator(true/*mayBeAbstract*/, false/*mayHaveIdentifier*/);

  // In case of an error, let the declaration parsing code handle it.
  if (TPR == TPResult::Error)
    TPR = TPResult::True;

  if (TPR == TPResult::Ambiguous) {
    // We are supposed to be inside parens, so if after the abstract declarator
    // we encounter a ')' this is a type-id, otherwise it's an expression.
    if (Context == TypeIdInParens && Tok.is(tok::r_paren)) {
      TPR = TPResult::True;
      isAmbiguous = true;

    // We are supposed to be inside a template argument, so if after
    // the abstract declarator we encounter a '>', '>>' (in C++0x), or
    // ','; or, in C++0x, an ellipsis immediately preceding such, this
    // is a type-id. Otherwise, it's an expression.
    } else if (Context == TypeIdAsTemplateArgument &&
               (Tok.isOneOf(tok::greater, tok::comma) ||
                (getLangOpts().CPlusPlus11 &&
                 (Tok.isOneOf(tok::greatergreater,
                              tok::greatergreatergreater) ||
                  (Tok.is(tok::ellipsis) &&
                   NextToken().isOneOf(tok::greater, tok::greatergreater,
                                       tok::greatergreatergreater,
                                       tok::comma)))))) {
      TPR = TPResult::True;
      isAmbiguous = true;

    } else
      TPR = TPResult::False;
  }

  assert(TPR == TPResult::True || TPR == TPResult::False);
  return TPR == TPResult::True;
}

/// Returns true if this is a C++11 attribute-specifier. Per
/// C++11 [dcl.attr.grammar]p6, two consecutive left square bracket tokens
/// always introduce an attribute. In Objective-C++11, this rule does not
/// apply if either '[' begins a message-send.
///
/// If Disambiguate is true, we try harder to determine whether a '[[' starts
/// an attribute-specifier, and return CAK_InvalidAttributeSpecifier if not.
///
/// If OuterMightBeMessageSend is true, we assume the outer '[' is either an
/// Obj-C message send or the start of an attribute. Otherwise, we assume it
/// is not an Obj-C message send.
///
/// C++11 [dcl.attr.grammar]:
///
///     attribute-specifier:
///         '[' '[' attribute-list ']' ']'
///         alignment-specifier
///
///     attribute-list:
///         attribute[opt]
///         attribute-list ',' attribute[opt]
///         attribute '...'
///         attribute-list ',' attribute '...'
///
///     attribute:
///         attribute-token attribute-argument-clause[opt]
///
///     attribute-token:
///         identifier
///         identifier '::' identifier
///
///     attribute-argument-clause:
///         '(' balanced-token-seq ')'
Parser::CXX11AttributeKind
Parser::isCXX11AttributeSpecifier(bool Disambiguate,
                                  bool OuterMightBeMessageSend) {
  if (Tok.is(tok::kw_alignas))
    return CAK_AttributeSpecifier;

  if (Tok.isNot(tok::l_square) || NextToken().isNot(tok::l_square))
    return CAK_NotAttributeSpecifier;

  // No tentative parsing if we don't need to look for ']]' or a lambda.
  if (!Disambiguate && !getLangOpts().ObjC)
    return CAK_AttributeSpecifier;

  // '[[using ns: ...]]' is an attribute.
  if (GetLookAheadToken(2).is(tok::kw_using))
    return CAK_AttributeSpecifier;

  RevertingTentativeParsingAction PA(*this);

  // Opening brackets were checked for above.
  ConsumeBracket();

  if (!getLangOpts().ObjC) {
    ConsumeBracket();

    bool IsAttribute = SkipUntil(tok::r_square);
    IsAttribute &= Tok.is(tok::r_square);

    return IsAttribute ? CAK_AttributeSpecifier : CAK_InvalidAttributeSpecifier;
  }

  // In Obj-C++11, we need to distinguish four situations:
  //  1a) int x[[attr]];                     C++11 attribute.
  //  1b) [[attr]];                          C++11 statement attribute.
  //   2) int x[[obj](){ return 1; }()];     Lambda in array size/index.
  //  3a) int x[[obj get]];                  Message send in array size/index.
  //  3b) [[Class alloc] init];              Message send in message send.
  //   4) [[obj]{ return self; }() doStuff]; Lambda in message send.
  // (1) is an attribute, (2) is ill-formed, and (3) and (4) are accepted.

  // Check to see if this is a lambda-expression.
  // FIXME: If this disambiguation is too slow, fold the tentative lambda parse
  // into the tentative attribute parse below.
  {
    RevertingTentativeParsingAction LambdaTPA(*this);
    LambdaIntroducer Intro;
    LambdaIntroducerTentativeParse Tentative;
    if (ParseLambdaIntroducer(Intro, &Tentative)) {
      // We hit a hard error after deciding this was not an attribute.
      // FIXME: Don't parse and annotate expressions when disambiguating
      // against an attribute.
      return CAK_NotAttributeSpecifier;
    }

    switch (Tentative) {
    case LambdaIntroducerTentativeParse::MessageSend:
      // Case 3: The inner construct is definitely a message send, so the
      // outer construct is definitely not an attribute.
      return CAK_NotAttributeSpecifier;

    case LambdaIntroducerTentativeParse::Success:
    case LambdaIntroducerTentativeParse::Incomplete:
      // This is a lambda-introducer or attribute-specifier.
      if (Tok.is(tok::r_square))
        // Case 1: C++11 attribute.
        return CAK_AttributeSpecifier;

      if (OuterMightBeMessageSend)
        // Case 4: Lambda in message send.
        return CAK_NotAttributeSpecifier;

      // Case 2: Lambda in array size / index.
      return CAK_InvalidAttributeSpecifier;

    case LambdaIntroducerTentativeParse::Invalid:
      // No idea what this is; we couldn't parse it as a lambda-introducer.
      // Might still be an attribute-specifier or a message send.
      break;
    }
  }

  ConsumeBracket();

  // If we don't have a lambda-introducer, then we have an attribute or a
  // message-send.
  bool IsAttribute = true;
  while (Tok.isNot(tok::r_square)) {
    if (Tok.is(tok::comma)) {
      // Case 1: Stray commas can only occur in attributes.
      return CAK_AttributeSpecifier;
    }

    // Parse the attribute-token, if present.
    // C++11 [dcl.attr.grammar]:
    //   If a keyword or an alternative token that satisfies the syntactic
    //   requirements of an identifier is contained in an attribute-token,
    //   it is considered an identifier.
    SourceLocation Loc;
    if (!TryParseCXX11AttributeIdentifier(Loc)) {
      IsAttribute = false;
      break;
    }
    if (Tok.is(tok::coloncolon)) {
      ConsumeToken();
      if (!TryParseCXX11AttributeIdentifier(Loc)) {
        IsAttribute = false;
        break;
      }
    }

    // Parse the attribute-argument-clause, if present.
    if (Tok.is(tok::l_paren)) {
      ConsumeParen();
      if (!SkipUntil(tok::r_paren)) {
        IsAttribute = false;
        break;
      }
    }

    TryConsumeToken(tok::ellipsis);

    if (!TryConsumeToken(tok::comma))
      break;
  }

  // An attribute must end ']]'.
  if (IsAttribute) {
    if (Tok.is(tok::r_square)) {
      ConsumeBracket();
      IsAttribute = Tok.is(tok::r_square);
    } else {
      IsAttribute = false;
    }
  }

  if (IsAttribute)
    // Case 1: C++11 statement attribute.
    return CAK_AttributeSpecifier;

  // Case 3: Message send.
  return CAK_NotAttributeSpecifier;
}

bool Parser::TrySkipAttributes() {
  while (Tok.isOneOf(tok::l_square, tok::kw___attribute, tok::kw___declspec,
                     tok::kw_alignas)) {
    if (Tok.is(tok::l_square)) {
      ConsumeBracket();
      if (Tok.isNot(tok::l_square))
        return false;
      ConsumeBracket();
      if (!SkipUntil(tok::r_square) || Tok.isNot(tok::r_square))
        return false;
      // Note that explicitly checking for `[[` and `]]` allows to fail as
      // expected in the case of the Objective-C message send syntax.
      ConsumeBracket();
    } else {
      ConsumeToken();
      if (Tok.isNot(tok::l_paren))
        return false;
      ConsumeParen();
      if (!SkipUntil(tok::r_paren))
        return false;
    }
  }

  return true;
}

Parser::TPResult Parser::TryParsePtrOperatorSeq() {
  while (true) {
    if (TryAnnotateOptionalCXXScopeToken(true))
      return TPResult::Error;

    if (Tok.isOneOf(tok::star, tok::amp, tok::caret, tok::ampamp) ||
        (Tok.is(tok::annot_cxxscope) && NextToken().is(tok::star))) {
      // ptr-operator
      ConsumeAnyToken();

      // Skip attributes.
      if (!TrySkipAttributes())
        return TPResult::Error;

      while (Tok.isOneOf(tok::kw_const, tok::kw_volatile, tok::kw_restrict,
                         tok::kw__Nonnull, tok::kw__Nullable,
                         tok::kw__Nullable_result, tok::kw__Null_unspecified,
                         tok::kw__Atomic))
        ConsumeToken();
    } else {
      return TPResult::True;
    }
  }
}

///         operator-function-id:
///           'operator' operator
///
///         operator: one of
///           new  delete  new[]  delete[]  +  -  *  /  %  ^  [...]
///
///         conversion-function-id:
///           'operator' conversion-type-id
///
///         conversion-type-id:
///           type-specifier-seq conversion-declarator[opt]
///
///         conversion-declarator:
///           ptr-operator conversion-declarator[opt]
///
///         literal-operator-id:
///           'operator' string-literal identifier
///           'operator' user-defined-string-literal
Parser::TPResult Parser::TryParseOperatorId() {
  assert(Tok.is(tok::kw_operator));
  ConsumeToken();

  // Maybe this is an operator-function-id.
  switch (Tok.getKind()) {
  case tok::kw_new: case tok::kw_delete:
    ConsumeToken();
    if (Tok.is(tok::l_square) && NextToken().is(tok::r_square)) {
      ConsumeBracket();
      ConsumeBracket();
    }
    return TPResult::True;

#define OVERLOADED_OPERATOR(Name, Spelling, Token, Unary, Binary, MemOnly) \
  case tok::Token:
#define OVERLOADED_OPERATOR_MULTI(Name, Spelling, Unary, Binary, MemOnly)
#include "clang/Basic/OperatorKinds.def"
    ConsumeToken();
    return TPResult::True;

  case tok::l_square:
    if (NextToken().is(tok::r_square)) {
      ConsumeBracket();
      ConsumeBracket();
      return TPResult::True;
    }
    break;

  case tok::l_paren:
    if (NextToken().is(tok::r_paren)) {
      ConsumeParen();
      ConsumeParen();
      return TPResult::True;
    }
    break;

  default:
    break;
  }

  // Maybe this is a literal-operator-id.
  if (getLangOpts().CPlusPlus11 && isTokenStringLiteral()) {
    bool FoundUDSuffix = false;
    do {
      FoundUDSuffix |= Tok.hasUDSuffix();
      ConsumeStringToken();
    } while (isTokenStringLiteral());

    if (!FoundUDSuffix) {
      if (Tok.is(tok::identifier))
        ConsumeToken();
      else
        return TPResult::Error;
    }
    return TPResult::True;
  }

  // Maybe this is a conversion-function-id.
  bool AnyDeclSpecifiers = false;
  while (true) {
    TPResult TPR = isCXXDeclarationSpecifier();
    if (TPR == TPResult::Error)
      return TPR;
    if (TPR == TPResult::False) {
      if (!AnyDeclSpecifiers)
        return TPResult::Error;
      break;
    }
    if (TryConsumeDeclarationSpecifier() == TPResult::Error)
      return TPResult::Error;
    AnyDeclSpecifiers = true;
  }
  return TryParsePtrOperatorSeq();
}

///         declarator:
///           direct-declarator
///           ptr-operator declarator
///
///         direct-declarator:
///           declarator-id
///           direct-declarator '(' parameter-declaration-clause ')'
///                 cv-qualifier-seq[opt] exception-specification[opt]
///           direct-declarator '[' constant-expression[opt] ']'
///           '(' declarator ')'
/// [GNU]     '(' attributes declarator ')'
///
///         abstract-declarator:
///           ptr-operator abstract-declarator[opt]
///           direct-abstract-declarator
///
///         direct-abstract-declarator:
///           direct-abstract-declarator[opt]
///                 '(' parameter-declaration-clause ')' cv-qualifier-seq[opt]
///                 exception-specification[opt]
///           direct-abstract-declarator[opt] '[' constant-expression[opt] ']'
///           '(' abstract-declarator ')'
/// [C++0x]   ...
///
///         ptr-operator:
///           '*' cv-qualifier-seq[opt]
///           '&'
/// [C++0x]   '&&'                                                        [TODO]
///           '::'[opt] nested-name-specifier '*' cv-qualifier-seq[opt]
///
///         cv-qualifier-seq:
///           cv-qualifier cv-qualifier-seq[opt]
///
///         cv-qualifier:
///           'const'
///           'volatile'
///
///         declarator-id:
///           '...'[opt] id-expression
///
///         id-expression:
///           unqualified-id
///           qualified-id                                                [TODO]
///
///         unqualified-id:
///           identifier
///           operator-function-id
///           conversion-function-id
///           literal-operator-id
///           '~' class-name                                              [TODO]
///           '~' decltype-specifier                                      [TODO]
///           template-id                                                 [TODO]
///
Parser::TPResult Parser::TryParseDeclarator(bool mayBeAbstract,
                                            bool mayHaveIdentifier,
                                            bool mayHaveDirectInit) {
  // declarator:
  //   direct-declarator
  //   ptr-operator declarator
  if (TryParsePtrOperatorSeq() == TPResult::Error)
    return TPResult::Error;

  // direct-declarator:
  // direct-abstract-declarator:
  if (Tok.is(tok::ellipsis))
    ConsumeToken();

#if ENABLE_BSC
  if (Tok.isOneOf(tok::kw_borrow, tok::kw_owned))
    ConsumeToken();
#endif

  if ((Tok.isOneOf(tok::identifier, tok::kw_operator) ||
       (Tok.is(tok::annot_cxxscope) && (NextToken().is(tok::identifier) ||
                                        NextToken().is(tok::kw_operator)))) &&
      mayHaveIdentifier) {
    // declarator-id
    if (Tok.is(tok::annot_cxxscope)) {
      CXXScopeSpec SS;
      Actions.RestoreNestedNameSpecifierAnnotation(
          Tok.getAnnotationValue(), Tok.getAnnotationRange(), SS);
      if (SS.isInvalid())
        return TPResult::Error;
      ConsumeAnnotationToken();
    } else if (Tok.is(tok::identifier)) {
      TentativelyDeclaredIdentifiers.push_back(Tok.getIdentifierInfo());
    }
    if (Tok.is(tok::kw_operator)) {
      if (TryParseOperatorId() == TPResult::Error)
        return TPResult::Error;
    } else
      ConsumeToken();
  } else if (Tok.is(tok::l_paren)) {
    ConsumeParen();
    if (mayBeAbstract &&
        (Tok.is(tok::r_paren) ||       // 'int()' is a function.
         // 'int(...)' is a function.
         (Tok.is(tok::ellipsis) && NextToken().is(tok::r_paren)) ||
         isDeclarationSpecifier())) {   // 'int(int)' is a function.
      // '(' parameter-declaration-clause ')' cv-qualifier-seq[opt]
      //        exception-specification[opt]
      TPResult TPR = TryParseFunctionDeclarator();
      if (TPR != TPResult::Ambiguous)
        return TPR;
    } else {
      // '(' declarator ')'
      // '(' attributes declarator ')'
      // '(' abstract-declarator ')'
      if (Tok.isOneOf(tok::kw___attribute, tok::kw___declspec, tok::kw___cdecl,
                      tok::kw___stdcall, tok::kw___fastcall, tok::kw___thiscall,
                      tok::kw___regcall, tok::kw___vectorcall))
        return TPResult::True; // attributes indicate declaration
      TPResult TPR = TryParseDeclarator(mayBeAbstract, mayHaveIdentifier);
      if (TPR != TPResult::Ambiguous)
        return TPR;
      if (Tok.isNot(tok::r_paren))
        return TPResult::False;
      ConsumeParen();
    }
  } else if (!mayBeAbstract) {
    return TPResult::False;
  }

  if (mayHaveDirectInit)
    return TPResult::Ambiguous;

  while (true) {
    TPResult TPR(TPResult::Ambiguous);

    if (Tok.is(tok::l_paren)) {
      // Check whether we have a function declarator or a possible ctor-style
      // initializer that follows the declarator. Note that ctor-style
      // initializers are not possible in contexts where abstract declarators
      // are allowed.
      if (!mayBeAbstract && !isCXXFunctionDeclarator())
        break;

      // direct-declarator '(' parameter-declaration-clause ')'
      //        cv-qualifier-seq[opt] exception-specification[opt]
      ConsumeParen();
      TPR = TryParseFunctionDeclarator();
    } else if (Tok.is(tok::l_square)) {
      // direct-declarator '[' constant-expression[opt] ']'
      // direct-abstract-declarator[opt] '[' constant-expression[opt] ']'
      TPR = TryParseBracketDeclarator();
    } else if (Tok.is(tok::kw_requires)) {
      // declarator requires-clause
      // A requires clause indicates a function declaration.
      TPR = TPResult::True;
    } else {
      break;
    }

    if (TPR != TPResult::Ambiguous)
      return TPR;
  }

  return TPResult::Ambiguous;
}

bool Parser::isTentativelyDeclared(IdentifierInfo *II) {
  return llvm::is_contained(TentativelyDeclaredIdentifiers, II);
}

#if ENABLE_BSC
// FIXME: Refactor!
// Check template declaration syntax in BSC:
//   function template declaration: "T Foo<T>(T a) {..}"
//   struct template declaration: "struct S<T> {..};"
//   struct template's method: "void struct S<T>::Foo();"
//   struct template's method: "void struct S<T>::Foo(){..};"
//   generic typealias declaration: "typedef S_T<T> = struct S<T>;"
// The method of checking template declaration is:
//   1. find template parameter list syntax structure "identifier <T, ..>"
//   2. find declaration syntax(different from spcialization syntax)
//     "<T, ..> ()" in template function, structure, typealias
bool Parser::isBSCTemplateDecl(Token tok) {
  // 1. check language
  if (!getLangOpts().BSC)
    return false;

  int LookAheadOffset = 0;
  bool FoundLess = false;
  bool FoundGreater = false;
  bool HasValidParameter = false;
  tok::TokenKind LookAheadKind =
                PP.LookAhead(LookAheadOffset).getKind();

  Token PreTok;
  Token NextTok;
  Token LookAheadTok;

  for (; !IsBSCTemplateBlackList(LookAheadKind); LookAheadOffset++) {
    LookAheadTok = PP.LookAhead(LookAheadOffset);
    LookAheadKind = PP.LookAhead(LookAheadOffset).getKind();
    if (IsBSCTemplateBlackList(LookAheadKind)) {
      break;
    }
    NextTok = PP.LookAhead(LookAheadOffset + 1);
    if (LookAheadOffset != 0) {
      PreTok = PP.LookAhead(LookAheadOffset - 1);
    } else {
      PreTok = Tok;
    }
    IdentifierInfo *CurName = LookAheadTok.getIdentifierInfo();
    SourceLocation CurNameLoc = LookAheadTok.getLocation();
    // lookup if identifier is a name of a struct/enum/union
    // for example:
    //     struct S {};
    //     struct T<struct S> foo(){}
    LookupResult LookupPreviousTag(Actions, CurName, CurNameLoc,
                                      Sema::LookupTagName, Sema::NotForRedeclaration);
    // lookup if identifier is a name of a typedef
    // for example:
    //     struct S {};
    //     typedef S S1;
    //     struct T<S1> foo(){}
    LookupResult LookupPreviousTypedef(Actions, CurName, CurNameLoc,
                                       Sema::LookupOrdinaryName, Sema::NotForRedeclaration);
    switch (LookAheadTok.getKind()) {
    case tok::less:
      if (PreTok.is(tok::identifier)) {
        // If already found less, or it`s a bit operation
        // case, like 'foo<(a<<b), int>;', skip it.
        if (FoundLess || (PreTok.is(tok::less) ||
                          NextTok.is(tok::less)))
          break;

        // To avoid the misjudgement of a none-return
        // BSC template function, like this:
        //    @Code
        //      void foo<T>(T a){};
        //      void test() {
        //        foo<int>(1);        // At here
        //      }
        //    @EndCode
        // Template struct will be distinguished at '>'.
        if (!(getCurScope()->getDepth() == 0) &&
            getCurScope()->getParent()->isClassScope())
          break;

        FoundLess = true;
      }
      break;
    case tok::l_paren:
      if (FoundLess)
      {
        return false;
      }
      break;
    case tok::greater:
      if (!FoundLess || (PreTok.is(tok::greater) ||
                         NextTok.is(tok::greater)))
        break;
      // valid syntax for BSC template
      if (HasValidParameter && NextTok.isOneOf(tok::l_brace, tok::l_paren,
                                               tok::semi, tok::coloncolon,
                                               tok::equal)) {
        FoundGreater = true;
        // These two typealias usecases are not allowed:
        //   "typedef struct S<T> {} S_T;"
        //   "typedef struct S<T> S_T;"
        if (Tok.is(tok::kw_typedef) && NextTok.isNot(tok::equal))
          return false;
        // Define a member function for a generic typealias is not allowed:
        //   typedef MyS<T> = struct S<T>;
        //   void MyS<T>::foo(This* this);
        if (!LookupPreviousTypedef.empty() && NextTok.is(tok::coloncolon))
          return false;
        return true;
      }
      break;
    case tok::identifier:
      // lookup this identifier
      Actions.LookupName(LookupPreviousTag, getCurScope());
      Actions.LookupName(LookupPreviousTypedef, getCurScope());

      // check if there is an identifier in "<>"
      // check if this identifier not found before
      if (LookupPreviousTag.empty() && LookupPreviousTypedef.empty() &&
          FoundLess && !FoundGreater) {
        HasValidParameter = true;
      }
      break;
    default:
      break;
    }
  }

  return false;
}
#endif

namespace {
class TentativeParseCCC final : public CorrectionCandidateCallback {
public:
  TentativeParseCCC(const Token &Next) {
    WantRemainingKeywords = false;
    WantTypeSpecifiers =
        Next.isOneOf(tok::l_paren, tok::r_paren, tok::greater, tok::l_brace,
                     tok::identifier, tok::comma);
  }

  bool ValidateCandidate(const TypoCorrection &Candidate) override {
    // Reject any candidate that only resolves to instance members since they
    // aren't viable as standalone identifiers instead of member references.
    if (Candidate.isResolved() && !Candidate.isKeyword() &&
        llvm::all_of(Candidate,
                     [](NamedDecl *ND) { return ND->isCXXInstanceMember(); }))
      return false;

    return CorrectionCandidateCallback::ValidateCandidate(Candidate);
  }

  std::unique_ptr<CorrectionCandidateCallback> clone() override {
    return std::make_unique<TentativeParseCCC>(*this);
  }
};
}
/// isCXXDeclarationSpecifier - Returns TPResult::True if it is a declaration
/// specifier, TPResult::False if it is not, TPResult::Ambiguous if it could
/// be either a decl-specifier or a function-style cast, and TPResult::Error
/// if a parsing error was found and reported.
///
/// If InvalidAsDeclSpec is not null, some cases that would be ill-formed as
/// declaration specifiers but possibly valid as some other kind of construct
/// return TPResult::Ambiguous instead of TPResult::False. When this happens,
/// the intent is to keep trying to disambiguate, on the basis that we might
/// find a better reason to treat this construct as a declaration later on.
/// When this happens and the name could possibly be valid in some other
/// syntactic context, *InvalidAsDeclSpec is set to 'true'. The current cases
/// that trigger this are:
///
///   * When parsing X::Y (with no 'typename') where X is dependent
///   * When parsing X<Y> where X is undeclared
///
///         decl-specifier:
///           storage-class-specifier
///           type-specifier
///           function-specifier
///           'friend'
///           'typedef'
/// [C++11]   'constexpr'
/// [C++20]   'consteval'
/// [GNU]     attributes declaration-specifiers[opt]
///
///         storage-class-specifier:
///           'register'
///           'static'
///           'extern'
///           'mutable'
///           'auto'
/// [GNU]     '__thread'
/// [C++11]   'thread_local'
/// [C11]     '_Thread_local'
///
///         function-specifier:
///           'inline'
///           'async'
///           'virtual'
///           'explicit'
///
///         typedef-name:
///           identifier
///
///         type-specifier:
///           simple-type-specifier
///           class-specifier
///           enum-specifier
///           elaborated-type-specifier
///           typename-specifier
///           cv-qualifier
///
///         simple-type-specifier:
///           '::'[opt] nested-name-specifier[opt] type-name
///           '::'[opt] nested-name-specifier 'template'
///                 simple-template-id                              [TODO]
///           'char'
///           'wchar_t'
///           'bool'
///           'short'
///           'int'
///           'long'
///           'signed'
///           'unsigned'
///           'float'
///           'double'
///           'void'
/// [GNU]     typeof-specifier
/// [GNU]     '_Complex'
/// [C++11]   'auto'
/// [GNU]     '__auto_type'
/// [C++11]   'decltype' ( expression )
/// [C++1y]   'decltype' ( 'auto' )
///
///         type-name:
///           class-name
///           enum-name
///           typedef-name
///
///         elaborated-type-specifier:
///           class-key '::'[opt] nested-name-specifier[opt] identifier
///           class-key '::'[opt] nested-name-specifier[opt] 'template'[opt]
///               simple-template-id
///           'enum' '::'[opt] nested-name-specifier[opt] identifier
///
///         enum-name:
///           identifier
///
///         enum-specifier:
///           'enum' identifier[opt] '{' enumerator-list[opt] '}'
///           'enum' identifier[opt] '{' enumerator-list ',' '}'
///
///         class-specifier:
///           class-head '{' member-specification[opt] '}'
///
///         class-head:
///           class-key identifier[opt] base-clause[opt]
///           class-key nested-name-specifier identifier base-clause[opt]
///           class-key nested-name-specifier[opt] simple-template-id
///               base-clause[opt]
///
///         class-key:
///           'class'
///           'struct'
///           'union'
///
///         cv-qualifier:
///           'const'
///           'volatile'
/// [GNU]     restrict
///
Parser::TPResult
Parser::isCXXDeclarationSpecifier(Parser::TPResult BracedCastResult,
                                  bool *InvalidAsDeclSpec) {
  auto IsPlaceholderSpecifier = [&] (TemplateIdAnnotation *TemplateId,
                                     int Lookahead) {
    // We have a placeholder-constraint (we check for 'auto' or 'decltype' to
    // distinguish 'C<int>;' from 'C<int> auto c = 1;')
    return TemplateId->Kind == TNK_Concept_template &&
        GetLookAheadToken(Lookahead + 1).isOneOf(tok::kw_auto, tok::kw_decltype,
            // If we have an identifier here, the user probably forgot the
            // 'auto' in the placeholder constraint, e.g. 'C<int> x = 2;'
            // This will be diagnosed nicely later, so disambiguate as a
            // declaration.
            tok::identifier);
  };
  switch (Tok.getKind()) {
  case tok::identifier: {
    // Check for need to substitute AltiVec __vector keyword
    // for "vector" identifier.
    if (TryAltiVecVectorToken())
      return TPResult::True;

    const Token &Next = NextToken();
    // In 'foo bar', 'foo' is always a type name outside of Objective-C.
    if (!getLangOpts().ObjC && Next.is(tok::identifier))
      return TPResult::True;

    if (Next.isNot(tok::coloncolon) && Next.isNot(tok::less)) {
      // Determine whether this is a valid expression. If not, we will hit
      // a parse error one way or another. In that case, tell the caller that
      // this is ambiguous. Typo-correct to type and expression keywords and
      // to types and identifiers, in order to try to recover from errors.
      TentativeParseCCC CCC(Next);
      switch (TryAnnotateName(&CCC)) {
      case ANK_Error:
        return TPResult::Error;
      case ANK_TentativeDecl:
        return TPResult::False;
      case ANK_TemplateName:
        // In C++17, this could be a type template for class template argument
        // deduction. Try to form a type annotation for it. If we're in a
        // template template argument, we'll undo this when checking the
        // validity of the argument.
        if (getLangOpts().CPlusPlus17) {
          if (TryAnnotateTypeOrScopeToken())
            return TPResult::Error;
          if (Tok.isNot(tok::identifier))
            break;
        }

        // A bare type template-name which can't be a template template
        // argument is an error, and was probably intended to be a type.
        return GreaterThanIsOperator ? TPResult::True : TPResult::False;
      case ANK_Unresolved:
        return InvalidAsDeclSpec ? TPResult::Ambiguous : TPResult::False;
      case ANK_Success:
        break;
      }
      assert(Tok.isNot(tok::identifier) &&
             "TryAnnotateName succeeded without producing an annotation");
    } else {
      // This might possibly be a type with a dependent scope specifier and
      // a missing 'typename' keyword. Don't use TryAnnotateName in this case,
      // since it will annotate as a primary expression, and we want to use the
      // "missing 'typename'" logic.
      if (TryAnnotateTypeOrScopeToken())
        return TPResult::Error;
      // If annotation failed, assume it's a non-type.
      // FIXME: If this happens due to an undeclared identifier, treat it as
      // ambiguous.
      if (Tok.is(tok::identifier))
        return TPResult::False;
    }

    // We annotated this token as something. Recurse to handle whatever we got.
    return isCXXDeclarationSpecifier(BracedCastResult, InvalidAsDeclSpec);
  }

  case tok::kw_typename:  // typename T::type
    // Annotate typenames and C++ scope specifiers.  If we get one, just
    // recurse to handle whatever we get.
    if (TryAnnotateTypeOrScopeToken())
      return TPResult::Error;
    return isCXXDeclarationSpecifier(BracedCastResult, InvalidAsDeclSpec);

  case tok::coloncolon: {    // ::foo::bar
    const Token &Next = NextToken();
    if (Next.isOneOf(tok::kw_new,       // ::new
                     tok::kw_delete))   // ::delete
      return TPResult::False;
    LLVM_FALLTHROUGH;
  }
  case tok::kw___super:
  case tok::kw_decltype:
    // Annotate typenames and C++ scope specifiers.  If we get one, just
    // recurse to handle whatever we get.
    if (TryAnnotateTypeOrScopeToken())
      return TPResult::Error;
    return isCXXDeclarationSpecifier(BracedCastResult, InvalidAsDeclSpec);

    // decl-specifier:
    //   storage-class-specifier
    //   type-specifier
    //   function-specifier
    //   'friend'
    //   'typedef'
    //   'constexpr'
  case tok::kw_friend:
  case tok::kw_typedef:
  case tok::kw_constexpr:
  case tok::kw_consteval:
  case tok::kw_constinit:
    // storage-class-specifier
  case tok::kw_register:
  case tok::kw_static:
  case tok::kw_extern:
  case tok::kw_mutable:
  case tok::kw_auto:
  case tok::kw___thread:
  case tok::kw_thread_local:
  case tok::kw__Thread_local:
    // function-specifier
  case tok::kw_inline:
#if ENABLE_BSC
  case tok::kw_async:
#endif
  case tok::kw_virtual:
  case tok::kw_explicit:

    // Modules
  case tok::kw___module_private__:

    // Debugger support
  case tok::kw___unknown_anytype:

    // type-specifier:
    //   simple-type-specifier
    //   class-specifier
    //   enum-specifier
    //   elaborated-type-specifier
    //   typename-specifier
    //   cv-qualifier

    // class-specifier
    // elaborated-type-specifier
  case tok::kw_class:
  case tok::kw_struct:
  case tok::kw_union:
#if ENABLE_BSC
  case tok::kw_trait:
#endif
  case tok::kw___interface:
    // enum-specifier
  case tok::kw_enum:
    // cv-qualifier
  case tok::kw_const:
  case tok::kw_volatile:
#if ENABLE_BSC
  case tok::kw_owned:
#endif
    return TPResult::True;

    // OpenCL address space qualifiers
  case tok::kw_private:
    if (!getLangOpts().OpenCL)
      return TPResult::False;
    LLVM_FALLTHROUGH;
  case tok::kw___private:
  case tok::kw___local:
  case tok::kw___global:
  case tok::kw___constant:
  case tok::kw___generic:
    // OpenCL access qualifiers
  case tok::kw___read_only:
  case tok::kw___write_only:
  case tok::kw___read_write:
    // OpenCL pipe
  case tok::kw_pipe:

    // GNU
  case tok::kw_restrict:
  case tok::kw__Complex:
  case tok::kw___attribute:
  case tok::kw___auto_type:
    return TPResult::True;

    // Microsoft
  case tok::kw___declspec:
  case tok::kw___cdecl:
  case tok::kw___stdcall:
  case tok::kw___fastcall:
  case tok::kw___thiscall:
  case tok::kw___regcall:
  case tok::kw___vectorcall:
  case tok::kw___w64:
  case tok::kw___sptr:
  case tok::kw___uptr:
  case tok::kw___ptr64:
  case tok::kw___ptr32:
  case tok::kw___forceinline:
  case tok::kw___unaligned:
  case tok::kw__Nonnull:
  case tok::kw__Nullable:
  case tok::kw__Nullable_result:
  case tok::kw__Null_unspecified:
  case tok::kw___kindof:
    return TPResult::True;

    // Borland
  case tok::kw___pascal:
    return TPResult::True;

    // AltiVec
  case tok::kw___vector:
    return TPResult::True;

  case tok::annot_template_id: {
    TemplateIdAnnotation *TemplateId = takeTemplateIdAnnotation(Tok);
    // If lookup for the template-name found nothing, don't assume we have a
    // definitive disambiguation result yet.
    if ((TemplateId->hasInvalidName() ||
         TemplateId->Kind == TNK_Undeclared_template) &&
        InvalidAsDeclSpec) {
      // 'template-id(' can be a valid expression but not a valid decl spec if
      // the template-name is not declared, but we don't consider this to be a
      // definitive disambiguation. In any other context, it's an error either
      // way.
      *InvalidAsDeclSpec = NextToken().is(tok::l_paren);
      return TPResult::Ambiguous;
    }
    if (TemplateId->hasInvalidName())
      return TPResult::Error;
    if (IsPlaceholderSpecifier(TemplateId, /*Lookahead=*/0))
      return TPResult::True;
    if (TemplateId->Kind != TNK_Type_template)
      return TPResult::False;
    CXXScopeSpec SS;
    AnnotateTemplateIdTokenAsType(SS);
    assert(Tok.is(tok::annot_typename));
    goto case_typename;
  }

  case tok::annot_cxxscope: // foo::bar or ::foo::bar, but already parsed
    // We've already annotated a scope; try to annotate a type.
    if (TryAnnotateTypeOrScopeToken())
      return TPResult::Error;
    if (!Tok.is(tok::annot_typename)) {
      if (Tok.is(tok::annot_cxxscope) &&
          NextToken().is(tok::annot_template_id)) {
        TemplateIdAnnotation *TemplateId =
            takeTemplateIdAnnotation(NextToken());
        if (TemplateId->hasInvalidName()) {
          if (InvalidAsDeclSpec) {
            *InvalidAsDeclSpec = NextToken().is(tok::l_paren);
            return TPResult::Ambiguous;
          }
          return TPResult::Error;
        }
        if (IsPlaceholderSpecifier(TemplateId, /*Lookahead=*/1))
          return TPResult::True;
      }
      // If the next token is an identifier or a type qualifier, then this
      // can't possibly be a valid expression either.
      if (Tok.is(tok::annot_cxxscope) && NextToken().is(tok::identifier)) {
        CXXScopeSpec SS;
        Actions.RestoreNestedNameSpecifierAnnotation(Tok.getAnnotationValue(),
                                                     Tok.getAnnotationRange(),
                                                     SS);
        if (SS.getScopeRep() && SS.getScopeRep()->isDependent()) {
          RevertingTentativeParsingAction PA(*this);
          ConsumeAnnotationToken();
          ConsumeToken();
          bool isIdentifier = Tok.is(tok::identifier);
          TPResult TPR = TPResult::False;
          if (!isIdentifier)
            TPR = isCXXDeclarationSpecifier(BracedCastResult,
                                            InvalidAsDeclSpec);

          if (isIdentifier ||
              TPR == TPResult::True || TPR == TPResult::Error)
            return TPResult::Error;

          if (InvalidAsDeclSpec) {
            // We can't tell whether this is a missing 'typename' or a valid
            // expression.
            *InvalidAsDeclSpec = true;
            return TPResult::Ambiguous;
          } else {
            // In MS mode, if InvalidAsDeclSpec is not provided, and the tokens
            // are or the form *) or &) *> or &> &&>, this can't be an expression.
            // The typename must be missing.
            if (getLangOpts().MSVCCompat) {
              if (((Tok.is(tok::amp) || Tok.is(tok::star)) &&
                   (NextToken().is(tok::r_paren) ||
                    NextToken().is(tok::greater))) ||
                  (Tok.is(tok::ampamp) && NextToken().is(tok::greater)))
                return TPResult::True;
            }
          }
        } else {
          // Try to resolve the name. If it doesn't exist, assume it was
          // intended to name a type and keep disambiguating.
          switch (TryAnnotateName()) {
          case ANK_Error:
            return TPResult::Error;
          case ANK_TentativeDecl:
            return TPResult::False;
          case ANK_TemplateName:
            // In C++17, this could be a type template for class template
            // argument deduction.
            if (getLangOpts().CPlusPlus17) {
              if (TryAnnotateTypeOrScopeToken())
                return TPResult::Error;
              if (Tok.isNot(tok::identifier))
                break;
            }

            // A bare type template-name which can't be a template template
            // argument is an error, and was probably intended to be a type.
            // In C++17, this could be class template argument deduction.
            return (getLangOpts().CPlusPlus17 || GreaterThanIsOperator)
                       ? TPResult::True
                       : TPResult::False;
          case ANK_Unresolved:
            return InvalidAsDeclSpec ? TPResult::Ambiguous : TPResult::False;
          case ANK_Success:
            break;
          }

          // Annotated it, check again.
          assert(Tok.isNot(tok::annot_cxxscope) ||
                 NextToken().isNot(tok::identifier));
          return isCXXDeclarationSpecifier(BracedCastResult, InvalidAsDeclSpec);
        }
      }
      return TPResult::False;
    }
    // If that succeeded, fallthrough into the generic simple-type-id case.
    LLVM_FALLTHROUGH;

    // The ambiguity resides in a simple-type-specifier/typename-specifier
    // followed by a '('. The '(' could either be the start of:
    //
    //   direct-declarator:
    //     '(' declarator ')'
    //
    //   direct-abstract-declarator:
    //     '(' parameter-declaration-clause ')' cv-qualifier-seq[opt]
    //              exception-specification[opt]
    //     '(' abstract-declarator ')'
    //
    // or part of a function-style cast expression:
    //
    //     simple-type-specifier '(' expression-list[opt] ')'
    //

    // simple-type-specifier:

  case tok::annot_typename:
  case_typename:
    // In Objective-C, we might have a protocol-qualified type.
    if (getLangOpts().ObjC && NextToken().is(tok::less)) {
      // Tentatively parse the protocol qualifiers.
      RevertingTentativeParsingAction PA(*this);
      ConsumeAnyToken(); // The type token

      TPResult TPR = TryParseProtocolQualifiers();
      bool isFollowedByParen = Tok.is(tok::l_paren);
      bool isFollowedByBrace = Tok.is(tok::l_brace);

      if (TPR == TPResult::Error)
        return TPResult::Error;

      if (isFollowedByParen)
        return TPResult::Ambiguous;

      if (getLangOpts().CPlusPlus11 && isFollowedByBrace)
        return BracedCastResult;

      return TPResult::True;
    }
    LLVM_FALLTHROUGH;

  case tok::kw_char:
  case tok::kw_wchar_t:
  case tok::kw_char8_t:
  case tok::kw_char16_t:
  case tok::kw_char32_t:
  case tok::kw_bool:
#if ENABLE_BSC
  case tok::kw__Bool:
#endif
  case tok::kw_short:
  case tok::kw_int:
  case tok::kw_long:
  case tok::kw___int64:
  case tok::kw___int128:
  case tok::kw_signed:
  case tok::kw_unsigned:
  case tok::kw_half:
  case tok::kw_float:
  case tok::kw_double:
  case tok::kw___bf16:
  case tok::kw__Float16:
  case tok::kw___float128:
  case tok::kw___ibm128:
  case tok::kw_void:
  case tok::annot_decltype:
#define GENERIC_IMAGE_TYPE(ImgType, Id) case tok::kw_##ImgType##_t:
#include "clang/Basic/OpenCLImageTypes.def"
    if (NextToken().is(tok::l_paren))
      return TPResult::Ambiguous;

    // This is a function-style cast in all cases we disambiguate other than
    // one:
    //   struct S {
    //     enum E : int { a = 4 }; // enum
    //     enum E : int { 4 };     // bit-field
    //   };
    if (getLangOpts().CPlusPlus11 && NextToken().is(tok::l_brace))
      return BracedCastResult;

    if (isStartOfObjCClassMessageMissingOpenBracket())
      return TPResult::False;

    return TPResult::True;

  // GNU typeof support.
  case tok::kw_typeof: {
    if (NextToken().isNot(tok::l_paren))
      return TPResult::True;

    RevertingTentativeParsingAction PA(*this);

    TPResult TPR = TryParseTypeofSpecifier();
    bool isFollowedByParen = Tok.is(tok::l_paren);
    bool isFollowedByBrace = Tok.is(tok::l_brace);

    if (TPR == TPResult::Error)
      return TPResult::Error;

    if (isFollowedByParen)
      return TPResult::Ambiguous;

    if (getLangOpts().CPlusPlus11 && isFollowedByBrace)
      return BracedCastResult;

    return TPResult::True;
  }

  // C++0x type traits support
  case tok::kw___underlying_type:
    return TPResult::True;

  // C11 _Atomic
  case tok::kw__Atomic:
    return TPResult::True;

  case tok::kw__BitInt:
  case tok::kw__ExtInt: {
    if (NextToken().isNot(tok::l_paren))
      return TPResult::Error;
    RevertingTentativeParsingAction PA(*this);
    ConsumeToken();
    ConsumeParen();

    if (!SkipUntil(tok::r_paren, StopAtSemi))
      return TPResult::Error;

    if (Tok.is(tok::l_paren))
      return TPResult::Ambiguous;

    if (getLangOpts().CPlusPlus11 && Tok.is(tok::l_brace))
      return BracedCastResult;

    return TPResult::True;
  }
  default:
    return TPResult::False;
  }
}

bool Parser::isCXXDeclarationSpecifierAType() {
  switch (Tok.getKind()) {
    // typename-specifier
  case tok::annot_decltype:
  case tok::annot_template_id:
  case tok::annot_typename:
  case tok::kw_typeof:
  case tok::kw___underlying_type:
    return true;

    // elaborated-type-specifier
  case tok::kw_class:
  case tok::kw_struct:
#if ENABLE_BSC
  case tok::kw_trait:
#endif
  case tok::kw_union:
  case tok::kw___interface:
  case tok::kw_enum:
    return true;

    // simple-type-specifier
  case tok::kw_char:
  case tok::kw_wchar_t:
  case tok::kw_char8_t:
  case tok::kw_char16_t:
  case tok::kw_char32_t:
  case tok::kw_bool:
  case tok::kw_short:
  case tok::kw_int:
  case tok::kw__ExtInt:
  case tok::kw__BitInt:
  case tok::kw_long:
  case tok::kw___int64:
  case tok::kw___int128:
  case tok::kw_signed:
  case tok::kw_unsigned:
  case tok::kw_half:
  case tok::kw_float:
  case tok::kw_double:
  case tok::kw___bf16:
  case tok::kw__Float16:
  case tok::kw___float128:
  case tok::kw___ibm128:
  case tok::kw_void:
  case tok::kw___unknown_anytype:
  case tok::kw___auto_type:
#define GENERIC_IMAGE_TYPE(ImgType, Id) case tok::kw_##ImgType##_t:
#include "clang/Basic/OpenCLImageTypes.def"
    return true;

  case tok::kw_auto:
    return getLangOpts().CPlusPlus11;

  case tok::kw__Atomic:
    // "_Atomic foo"
    return NextToken().is(tok::l_paren);

  default:
    return false;
  }
}

/// [GNU] typeof-specifier:
///         'typeof' '(' expressions ')'
///         'typeof' '(' type-name ')'
///
Parser::TPResult Parser::TryParseTypeofSpecifier() {
  assert(Tok.is(tok::kw_typeof) && "Expected 'typeof'!");
  ConsumeToken();

  assert(Tok.is(tok::l_paren) && "Expected '('");
  // Parse through the parens after 'typeof'.
  ConsumeParen();
  if (!SkipUntil(tok::r_paren, StopAtSemi))
    return TPResult::Error;

  return TPResult::Ambiguous;
}

/// [ObjC] protocol-qualifiers:
////         '<' identifier-list '>'
Parser::TPResult Parser::TryParseProtocolQualifiers() {
  assert(Tok.is(tok::less) && "Expected '<' for qualifier list");
  ConsumeToken();
  do {
    if (Tok.isNot(tok::identifier))
      return TPResult::Error;
    ConsumeToken();

    if (Tok.is(tok::comma)) {
      ConsumeToken();
      continue;
    }

    if (Tok.is(tok::greater)) {
      ConsumeToken();
      return TPResult::Ambiguous;
    }
  } while (false);

  return TPResult::Error;
}

/// isCXXFunctionDeclarator - Disambiguates between a function declarator or
/// a constructor-style initializer, when parsing declaration statements.
/// Returns true for function declarator and false for constructor-style
/// initializer.
/// If during the disambiguation process a parsing error is encountered,
/// the function returns true to let the declaration parsing code handle it.
///
/// '(' parameter-declaration-clause ')' cv-qualifier-seq[opt]
///         exception-specification[opt]
///
bool Parser::isCXXFunctionDeclarator(bool *IsAmbiguous) {

  // C++ 8.2p1:
  // The ambiguity arising from the similarity between a function-style cast and
  // a declaration mentioned in 6.8 can also occur in the context of a
  // declaration. In that context, the choice is between a function declaration
  // with a redundant set of parentheses around a parameter name and an object
  // declaration with a function-style cast as the initializer. Just as for the
  // ambiguities mentioned in 6.8, the resolution is to consider any construct
  // that could possibly be a declaration a declaration.

  RevertingTentativeParsingAction PA(*this);

  ConsumeParen();
  bool InvalidAsDeclaration = false;
  TPResult TPR = TryParseParameterDeclarationClause(&InvalidAsDeclaration);
  if (TPR == TPResult::Ambiguous) {
    if (Tok.isNot(tok::r_paren))
      TPR = TPResult::False;
    else {
      const Token &Next = NextToken();
      if (Next.isOneOf(tok::amp, tok::ampamp, tok::kw_const, tok::kw_volatile,
                       tok::kw_throw, tok::kw_noexcept, tok::l_square,
                       tok::l_brace, tok::kw_try, tok::equal, tok::arrow) ||
          isCXX11VirtSpecifier(Next))
        // The next token cannot appear after a constructor-style initializer,
        // and can appear next in a function definition. This must be a function
        // declarator.
        TPR = TPResult::True;
      else if (InvalidAsDeclaration)
        // Use the absence of 'typename' as a tie-breaker.
        TPR = TPResult::False;
    }
  }

  if (IsAmbiguous && TPR == TPResult::Ambiguous)
    *IsAmbiguous = true;

  // In case of an error, let the declaration parsing code handle it.
  return TPR != TPResult::False;
}

/// parameter-declaration-clause:
///   parameter-declaration-list[opt] '...'[opt]
///   parameter-declaration-list ',' '...'
///
/// parameter-declaration-list:
///   parameter-declaration
///   parameter-declaration-list ',' parameter-declaration
///
/// parameter-declaration:
///   attribute-specifier-seq[opt] decl-specifier-seq declarator attributes[opt]
///   attribute-specifier-seq[opt] decl-specifier-seq declarator attributes[opt]
///     '=' assignment-expression
///   attribute-specifier-seq[opt] decl-specifier-seq abstract-declarator[opt]
///     attributes[opt]
///   attribute-specifier-seq[opt] decl-specifier-seq abstract-declarator[opt]
///     attributes[opt] '=' assignment-expression
///
Parser::TPResult
Parser::TryParseParameterDeclarationClause(bool *InvalidAsDeclaration,
                                           bool VersusTemplateArgument) {

  if (Tok.is(tok::r_paren))
    return TPResult::Ambiguous;

  //   parameter-declaration-list[opt] '...'[opt]
  //   parameter-declaration-list ',' '...'
  //
  // parameter-declaration-list:
  //   parameter-declaration
  //   parameter-declaration-list ',' parameter-declaration
  //
  while (true) {
    // '...'[opt]
    if (Tok.is(tok::ellipsis)) {
      ConsumeToken();
      if (Tok.is(tok::r_paren))
        return TPResult::True; // '...)' is a sign of a function declarator.
      else
        return TPResult::False;
    }

    // An attribute-specifier-seq here is a sign of a function declarator.
    if (isCXX11AttributeSpecifier(/*Disambiguate*/false,
                                  /*OuterMightBeMessageSend*/true))
      return TPResult::True;

    ParsedAttributes attrs(AttrFactory);
    MaybeParseMicrosoftAttributes(attrs);

    // decl-specifier-seq
    // A parameter-declaration's initializer must be preceded by an '=', so
    // decl-specifier-seq '{' is not a parameter in C++11.
    TPResult TPR = isCXXDeclarationSpecifier(TPResult::False,
                                             InvalidAsDeclaration);
    // A declaration-specifier (not followed by '(' or '{') means this can't be
    // an expression, but it could still be a template argument.
    if (TPR != TPResult::Ambiguous &&
        !(VersusTemplateArgument && TPR == TPResult::True))
      return TPR;

    bool SeenType = false;
    do {
      SeenType |= isCXXDeclarationSpecifierAType();
      if (TryConsumeDeclarationSpecifier() == TPResult::Error)
        return TPResult::Error;

      // If we see a parameter name, this can't be a template argument.
      if (SeenType && Tok.is(tok::identifier))
        return TPResult::True;

      TPR = isCXXDeclarationSpecifier(TPResult::False,
                                      InvalidAsDeclaration);
      if (TPR == TPResult::Error)
        return TPR;

      // Two declaration-specifiers means this can't be an expression.
      if (TPR == TPResult::True && !VersusTemplateArgument)
        return TPR;
    } while (TPR != TPResult::False);

    // declarator
    // abstract-declarator[opt]
    TPR = TryParseDeclarator(true/*mayBeAbstract*/);
    if (TPR != TPResult::Ambiguous)
      return TPR;

    // [GNU] attributes[opt]
    if (Tok.is(tok::kw___attribute))
      return TPResult::True;

    // If we're disambiguating a template argument in a default argument in
    // a class definition versus a parameter declaration, an '=' here
    // disambiguates the parse one way or the other.
    // If this is a parameter, it must have a default argument because
    //   (a) the previous parameter did, and
    //   (b) this must be the first declaration of the function, so we can't
    //       inherit any default arguments from elsewhere.
    // FIXME: If we reach a ')' without consuming any '>'s, then this must
    // also be a function parameter (that's missing its default argument).
    if (VersusTemplateArgument)
      return Tok.is(tok::equal) ? TPResult::True : TPResult::False;

    if (Tok.is(tok::equal)) {
      // '=' assignment-expression
      // Parse through assignment-expression.
      if (!SkipUntil(tok::comma, tok::r_paren, StopAtSemi | StopBeforeMatch))
        return TPResult::Error;
    }

    if (Tok.is(tok::ellipsis)) {
      ConsumeToken();
      if (Tok.is(tok::r_paren))
        return TPResult::True; // '...)' is a sign of a function declarator.
      else
        return TPResult::False;
    }

    if (!TryConsumeToken(tok::comma))
      break;
  }

  return TPResult::Ambiguous;
}

/// TryParseFunctionDeclarator - We parsed a '(' and we want to try to continue
/// parsing as a function declarator.
/// If TryParseFunctionDeclarator fully parsed the function declarator, it will
/// return TPResult::Ambiguous, otherwise it will return either False() or
/// Error().
///
/// '(' parameter-declaration-clause ')' cv-qualifier-seq[opt]
///         exception-specification[opt]
///
/// exception-specification:
///   'throw' '(' type-id-list[opt] ')'
///
Parser::TPResult Parser::TryParseFunctionDeclarator() {
  // The '(' is already parsed.

  TPResult TPR = TryParseParameterDeclarationClause();
  if (TPR == TPResult::Ambiguous && Tok.isNot(tok::r_paren))
    TPR = TPResult::False;

  if (TPR == TPResult::False || TPR == TPResult::Error)
    return TPR;

  // Parse through the parens.
  if (!SkipUntil(tok::r_paren, StopAtSemi))
    return TPResult::Error;

  // cv-qualifier-seq
  while (Tok.isOneOf(tok::kw_const, tok::kw_volatile, tok::kw___unaligned,
                     tok::kw_restrict))
    ConsumeToken();

  // ref-qualifier[opt]
  if (Tok.isOneOf(tok::amp, tok::ampamp))
    ConsumeToken();

  // exception-specification
  if (Tok.is(tok::kw_throw)) {
    ConsumeToken();
    if (Tok.isNot(tok::l_paren))
      return TPResult::Error;

    // Parse through the parens after 'throw'.
    ConsumeParen();
    if (!SkipUntil(tok::r_paren, StopAtSemi))
      return TPResult::Error;
  }
  if (Tok.is(tok::kw_noexcept)) {
    ConsumeToken();
    // Possibly an expression as well.
    if (Tok.is(tok::l_paren)) {
      // Find the matching rparen.
      ConsumeParen();
      if (!SkipUntil(tok::r_paren, StopAtSemi))
        return TPResult::Error;
    }
  }

  return TPResult::Ambiguous;
}

/// '[' constant-expression[opt] ']'
///
Parser::TPResult Parser::TryParseBracketDeclarator() {
  ConsumeBracket();

  // A constant-expression cannot begin with a '{', but the
  // expr-or-braced-init-list of a postfix-expression can.
  if (Tok.is(tok::l_brace))
    return TPResult::False;

  if (!SkipUntil(tok::r_square, tok::comma, StopAtSemi | StopBeforeMatch))
    return TPResult::Error;

  // If we hit a comma before the ']', this is not a constant-expression,
  // but might still be the expr-or-braced-init-list of a postfix-expression.
  if (Tok.isNot(tok::r_square))
    return TPResult::False;

  ConsumeBracket();
  return TPResult::Ambiguous;
}

/// Determine whether we might be looking at the '<' template-argument-list '>'
/// of a template-id or simple-template-id, rather than a less-than comparison.
/// This will often fail and produce an ambiguity, but should never be wrong
/// if it returns True or False.
Parser::TPResult Parser::isTemplateArgumentList(unsigned TokensToSkip) {
  if (!TokensToSkip) {
    if (Tok.isNot(tok::less))
      return TPResult::False;
    if (NextToken().is(tok::greater))
      return TPResult::True;
  }

  RevertingTentativeParsingAction PA(*this);

  while (TokensToSkip) {
    ConsumeAnyToken();
    --TokensToSkip;
  }

  if (!TryConsumeToken(tok::less))
    return TPResult::False;

  // We can't do much to tell an expression apart from a template-argument,
  // but one good distinguishing factor is that a "decl-specifier" not
  // followed by '(' or '{' can't appear in an expression.
  bool InvalidAsTemplateArgumentList = false;
  if (isCXXDeclarationSpecifier(TPResult::False,
                                       &InvalidAsTemplateArgumentList) ==
             TPResult::True)
    return TPResult::True;
  if (InvalidAsTemplateArgumentList)
    return TPResult::False;

  // FIXME: In many contexts, X<thing1, Type> can only be a
  // template-argument-list. But that's not true in general:
  //
  // using b = int;
  // void f() {
  //   int a = A<B, b, c = C>D; // OK, declares b, not a template-id.
  //
  // X<Y<0, int> // ', int>' might be end of X's template argument list
  //
  // We might be able to disambiguate a few more cases if we're careful.

  // A template-argument-list must be terminated by a '>'.
  if (SkipUntil({tok::greater, tok::greatergreater, tok::greatergreatergreater},
                StopAtSemi | StopBeforeMatch))
    return TPResult::Ambiguous;
  return TPResult::False;
}

/// Determine whether we might be looking at the '(' of a C++20 explicit(bool)
/// in an earlier language mode.
Parser::TPResult Parser::isExplicitBool() {
  assert(Tok.is(tok::l_paren) && "expected to be looking at a '(' token");

  RevertingTentativeParsingAction PA(*this);
  ConsumeParen();

  // We can only have 'explicit' on a constructor, conversion function, or
  // deduction guide. The declarator of a deduction guide cannot be
  // parenthesized, so we know this isn't a deduction guide. So the only
  // thing we need to check for is some number of parens followed by either
  // the current class name or 'operator'.
  while (Tok.is(tok::l_paren))
    ConsumeParen();

  if (TryAnnotateOptionalCXXScopeToken())
    return TPResult::Error;

  // Class-scope constructor and conversion function names can't really be
  // qualified, but we get better diagnostics if we assume they can be.
  CXXScopeSpec SS;
  if (Tok.is(tok::annot_cxxscope)) {
    Actions.RestoreNestedNameSpecifierAnnotation(Tok.getAnnotationValue(),
                                                 Tok.getAnnotationRange(),
                                                 SS);
    ConsumeAnnotationToken();
  }

  // 'explicit(operator' might be explicit(bool) or the declaration of a
  // conversion function, but it's probably a conversion function.
  if (Tok.is(tok::kw_operator))
    return TPResult::Ambiguous;

  // If this can't be a constructor name, it can only be explicit(bool).
  if (Tok.isNot(tok::identifier) && Tok.isNot(tok::annot_template_id))
    return TPResult::True;
  if (!Actions.isCurrentClassName(Tok.is(tok::identifier)
                                      ? *Tok.getIdentifierInfo()
                                      : *takeTemplateIdAnnotation(Tok)->Name,
                                  getCurScope(), &SS))
    return TPResult::True;
  // Formally, we must have a right-paren after the constructor name to match
  // the grammar for a constructor. But clang permits a parenthesized
  // constructor declarator, so also allow a constructor declarator to follow
  // with no ')' token after the constructor name.
  if (!NextToken().is(tok::r_paren) &&
      !isConstructorDeclarator(/*Unqualified=*/SS.isEmpty(),
                               /*DeductionGuide=*/false))
    return TPResult::True;

  // Might be explicit(bool) or a parenthesized constructor name.
  return TPResult::Ambiguous;
}
