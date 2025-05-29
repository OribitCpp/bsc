//===--- AddNewFieldCheck.h - clang-tidy ------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_BSC_ADDNEWFIELDCHECK_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_BSC_ADDNEWFIELDCHECK_H

#include "../ClangTidyCheck.h"

namespace clang {
namespace tidy {
namespace bsc {

/// FIXME: Write a short description.
///
/// For the user-facing documentation see:
/// http://clang.llvm.org/extra/clang-tidy/checks/bsc/add-new-field.html
class AddNewFieldCheck : public ClangTidyCheck {
public:
  AddNewFieldCheck(StringRef Name, ClangTidyContext *Context)
      : ClangTidyCheck(Name, Context),
        TargetStructList(Options.get("TargetStructs", "TEMP_FAILURE_RETRY")) {
    StringRef(TargetStructList).split(TargetStructs, ",", -1, false);
  }
  void storeOptions(ClangTidyOptions::OptionMap &Opts) {
    Options.store(Opts, "TargetStructs", TargetStructList);
  }
  void registerMatchers(ast_matchers::MatchFinder *Finder) override;
  void check(const ast_matchers::MatchFinder::MatchResult &Result) override;

private:
  const StringRef TargetStructList;
  SmallVector<StringRef, 5> TargetStructs;
};

} // namespace bsc
} // namespace tidy
} // namespace clang

#endif // LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_BSC_ADDNEWFIELDCHECK_H
