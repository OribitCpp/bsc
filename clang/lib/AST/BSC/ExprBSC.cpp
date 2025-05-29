//===- ExprBSC.cpp - BSC Expression AST Node Implementation --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the BSC related Expr classes.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/AST/BSC/ExprBSC.h"
#include "clang/AST/ASTContext.h"
#include "clang/Basic/Linkage.h"

using namespace clang;

/// If current expr is equal to 0, return true.
/// Such as : nullptr, 0, (void*)0, ((void*)0), (int*)0,
///           (int* borrow)(void*)0, (int* owned)(void*)0,
/// also include constant value which equals to 0.
bool Expr::isNullExpr(ASTContext &Ctx) const {
  if (getType()->isNullPtrType()) {
    return true;
  } else if (const IntegerLiteral *IL = dyn_cast<IntegerLiteral>(this)) {
    if (IL->getValue().getZExtValue() == 0)
      return true;
  } else if (const CStyleCastExpr *CSCE = dyn_cast<CStyleCastExpr>(this)) {
    return CSCE->getSubExpr()->isNullExpr(Ctx);
  } else if (const ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(this)) {
    return ICE->getSubExpr()->isNullExpr(Ctx);
  } else if (const ParenExpr *PE = dyn_cast<ParenExpr>(this)) {
    return PE->getSubExpr()->isNullExpr(Ctx);
  } else if (Optional<llvm::APSInt> I = this->getIntegerConstantExpr(Ctx)) {
    if (*I == 0)
      return true;
  }
  return false;
}
#endif // ENABLE_BSC