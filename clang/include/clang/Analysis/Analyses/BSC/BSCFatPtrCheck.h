//===- BSCFatPtrCheck.h - FatPtr Check Reduntant Analysis for Source CFGs -*- BSC ---*//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements BSC Fat Pointer Check Reduntant Analysis for source-level CFGs.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ANALYSIS_ANALYSES_BSCFATPTRCHECK_H
#define LLVM_CLANG_ANALYSIS_ANALYSES_BSCFATPTRCHECK_H

#if ENABLE_BSC

#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CallGraph.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Sema/Sema.h"

namespace clang {
void runFatPtrReduntantCheck(const FunctionDecl &fd, const CFG &cfg,
                    AnalysisDeclContext &ac, ASTContext &ctx);
}

#endif // ENABLE_BSC

#endif // LLVM_CLANG_ANALYSIS_ANALYSES_BSCFATPTRCHECK_H