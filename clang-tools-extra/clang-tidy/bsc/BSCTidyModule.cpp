//===------- BSCTidyModule.cpp - clang-tidy -----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "../ClangTidy.h"
#include "../ClangTidyModule.h"
#include "../ClangTidyModuleRegistry.h"
#include "AccessSpecificTypeCheck.h"
#include "AddNewFieldCheck.h"
#include "ExplicitCastCheck.h"

namespace clang {
namespace tidy {
namespace bsc {

class BscModule : public ClangTidyModule {
public:
  void addCheckFactories(ClangTidyCheckFactories &CheckFactories) override {
    CheckFactories.registerCheck<AccessSpecificTypeCheck>(
        "bsc-access-specific-type");
    CheckFactories.registerCheck<AddNewFieldCheck>(
        "bsc-add-new-field");
    CheckFactories.registerCheck<ExplicitCastCheck>(
        "bsc-explicit-cast");
  }
};

// Register the BscModule using this statically initialized variable.
static ClangTidyModuleRegistry::Add<BscModule> X("bsc-module",
                                                   "Add bsc checks.");

} // namespace bsc

// This anchor is used to force the linker to link in the generated object file
// and thus register the BscModule.
volatile int BscModuleAnchorSource = 0;

} // namespace tidy
} // namespace clang
