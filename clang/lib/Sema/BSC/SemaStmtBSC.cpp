//===--- SemaStmtBSC.cpp - Semantic Analysis for Statements
//------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file implements semantic analysis for statements.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/Sema/Sema.h"
#include "clang/Sema/SemaDiagnostic.h"

using namespace clang;
using namespace sema;

void Sema::ActOnPragmaSafe(PragmaSafeStatus St) {
  SafeScopeSpecifier spec = St == PSS_On ? SS_Safe : SS_Unsafe;
  SetPragmaSafeInfo(spec);
}

void Sema::ActOnPragmaPreferInline(PragmaPreferInlineStatus St) {
  PreferInlineScopeSpecifier spec = PI_None;
  if (St == PPI_On) {
    spec = PI_PreferInline;
  } else if (St == PPI_Off) {
    spec = PI_PreferNoInline;
  }
  SetPragmaPreferInlineInfo(spec);
}

void Sema::ActOnPragmaIcallHint(std::string funcInfo) {
  if (funcInfo.size() != 0) {
    SetVTableIcallHintInfos(funcInfo);
  }
}

// Check if BSC constexpr if condition expression satisfy:
// 1. type is bool, integral or char;
// 2. constant expression which can be calculated in compile time.
ExprResult Sema::CheckBSCConstexprCondition(SourceLocation Loc, Expr *CondExpr, bool IsConstexpr) {
  if (!CondExpr->getType()->isBSCCalculatedTypeInCompileTime()) {
    Diag(Loc, diag::err_constexpr_if_cond_expr_unsupported_type) << CondExpr->getType();
    return ExprError();
  }
  return CheckCXXBooleanCondition(CondExpr, IsConstexpr);
}
#endif