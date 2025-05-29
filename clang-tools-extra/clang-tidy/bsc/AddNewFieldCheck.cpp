//===--- AddNewFieldCheck.cpp - clang-tidy --------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "AddNewFieldCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"

using namespace clang::ast_matchers;
namespace clang {
namespace tidy {
namespace bsc {

void AddNewFieldCheck::registerMatchers(MatchFinder *Finder) {
  for (auto TargetStruct : TargetStructs) {
    Finder->addMatcher(
        recordDecl(has(fieldDecl(hasType(asString(std::string(TargetStruct))))
                           .bind("x")))
            .bind("y"),
        this);
  }
}

void AddNewFieldCheck::check(const MatchFinder::MatchResult &Result) {
  const auto *MatchedDecl1 = Result.Nodes.getNodeAs<RecordDecl>("y");

  for (auto* DeclField : MatchedDecl1->fields()) {
    bool IsAlreadyExsit = false;
    std::string Identifier = std::string(DeclField->getName());
    std::string Expected_Name = "__" + Identifier + "_DBID";

    for (auto TargetStruct : TargetStructs) {
      if (DeclField->getType().getAsString() == std::string(TargetStruct)) {
        for (auto* SingleField : MatchedDecl1->fields()) {
          if (std::string(SingleField->getName()) == Expected_Name) {
            diag(MatchedDecl1->getLocation(), "no need", DiagnosticIDs::Note);
            IsAlreadyExsit = true;
            break;
          }
        }

        if (IsAlreadyExsit) {
          break;
        } else {
          SourceLocation SL = DeclField->getSourceRange().getEnd().getLocWithOffset(Identifier.length()+1);
          diag(SL, "insert __DBID field", DiagnosticIDs::Warning)
              << FixItHint::CreateInsertion(SL, "\n\tvoid* __" + Identifier + "_DBID;");
        }
      }
    }
  }
}

} // namespace bsc
} // namespace tidy
} // namespace clang
