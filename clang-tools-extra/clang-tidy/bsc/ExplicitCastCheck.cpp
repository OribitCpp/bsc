//===--- ExplicitCastCheck.cpp - clang-tidy -------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "ExplicitCastCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"

using namespace clang::ast_matchers;

namespace clang {
namespace tidy {
namespace bsc {

void ExplicitCastCheck::registerMatchers(MatchFinder *Finder) {
  for (auto TargetStruct : TargetStructs) {
    // Targets cast to others.
    Finder->addMatcher(cStyleCastExpr(hasSourceExpression(hasType(
                                          asString(std::string(TargetStruct)))))
                           .bind("x"),
                       this);
    // Others cast to targets.
    Finder->addMatcher(cStyleCastExpr(hasType(asString(std::string(TargetStruct)))).bind("y"), this);
  }
}

void ExplicitCastCheck::check(const MatchFinder::MatchResult &Result) {
  const auto *CastFromTargetType = Result.Nodes.getNodeAs<CStyleCastExpr>("x");
  const auto *CastToTargetType = Result.Nodes.getNodeAs<CStyleCastExpr>("y");

  if (CastFromTargetType) {
    const Expr* SubExpr = CastFromTargetType->getSubExpr();
    std::string CastTypeName = SubExpr->getType().getAsString();
    SourceLocation SL = CastFromTargetType->getSourceRange().getEnd();
    diag(SL, "Find explicit cast from target type: " + CastTypeName, DiagnosticIDs::Warning);
  }

  if (CastToTargetType) {
    std::string CastTypeName = CastToTargetType->getType().getAsString();
    SourceLocation SL = CastToTargetType->getSourceRange().getEnd();
    diag(SL, "Find explicit cast to target type: " + CastTypeName, DiagnosticIDs::Warning);
  }
}

} // namespace bsc
} // namespace tidy
} // namespace clang
