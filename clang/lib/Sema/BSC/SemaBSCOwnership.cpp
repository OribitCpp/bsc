//===--- SemaBSCOwnership.cpp - Semantic Analysis for BSC Ownership
//----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file implements dataflow analysis for BSC Ownership.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/AST/Type.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/SemaDiagnostic.h"

using namespace clang;
using namespace sema;

// for union fields/array/global variable type check
void Sema::CheckOwnedOrIndirectOwnedType(SourceLocation ErrLoc, QualType T, StringRef Env) {
  enum {
    ownedQualified,
    ownedTypedef,
    ownedFields
  };
  if (T.getCanonicalType().isOwnedQualified() && !T.getTypePtr()->getAs<TypedefType>()) {
    Diag(ErrLoc, diag::err_owned_inderictOwned_type_check)
        << ownedQualified << "owned" << Env;
  } else if (T.getCanonicalType().isOwnedQualified() && T.getTypePtr()->getAs<TypedefType>()) {
    Diag(ErrLoc, diag::err_owned_inderictOwned_type_check)
        << ownedTypedef << "owned" << Env << T;
  } else if (T.getCanonicalType().getTypePtr()->isMoveSemanticType()) {
    Diag(ErrLoc, diag::err_owned_inderictOwned_type_check)
        << ownedFields << "owned" << Env << T;
  }
}

bool Sema::CheckOwnedDecl(SourceLocation ErrLoc, QualType T) {
  // owned union check
  if (T.getCanonicalType()->isUnionType()) {
    Diag(ErrLoc, diag::err_owned_decl) << T;
    return false;
  }
  return true;
}

bool Sema::CheckOwnedQualTypeCStyleCast(QualType LHSType, QualType RHSType) {
  QualType RHSCanType = RHSType.getCanonicalType();
  QualType LHSCanType = LHSType.getCanonicalType();
  bool IsSameType = (LHSCanType.getTypePtr() == RHSCanType.getTypePtr());
  const auto *LHSPtrType = LHSType->getAs<PointerType>();
  const auto *RHSPtrType = RHSType->getAs<PointerType>();
  bool IsPointer = LHSPtrType && RHSPtrType;

  if (RHSCanType->isDependentType()) {
    return true;
  }

  // legal cases:
  // 'int owned'    <->  'int owned'                      // same type same owned
  // 'int'          <->  'owned int'                      // same type diff owned
  // 'owned int*'   <->  'int*'                           // pointer to 'same type diff owned'
  // 'int**'        <->  'owned int* const owned * owned' // multi-layer pointer same type diff owned or const
  // 'int**'        <->  'int* const * owned'             // multi-layer pointer same type diff owned or const
  // 'float* owned' <->  'void* owned'                    // pointer to diff type but voidpointer same owned
  // 'float* owned' <->  'void*'                          // diff type but voidpointer diff owned
  // 'int** owned'' <->  const int** owned'

  // illegal cases:
  // 'float owned'  <->  'int owned'    // diff type
  // 'float* owned' <->  'int* owned'   // diff type same owned
  // 'owned float*' <->  'owned int*'   // pointer to diff type same owned
  // 'int'          <->  'void* owned'  //

  if (IsSameType) {
    return true;
  }
  if (IsPointer) {
    if (LHSCanType.getTypePtr()->isVoidPointerType() || RHSCanType.getTypePtr()->isVoidPointerType()) {
      return true;
    } else {
      return CheckOwnedQualTypeCStyleCast(LHSPtrType->getPointeeType(), RHSPtrType->getPointeeType());
    }
  }
  return false;
}

bool Sema::CheckOwnedQualTypeCStyleCast(QualType LHSType, QualType RHSType, SourceLocation RLoc) {
  if (!CheckOwnedQualTypeCStyleCast(LHSType, RHSType)) {
    Diag(RLoc, diag::err_owned_qualcheck_incompatible) << RHSType << LHSType;
    return false;
  } else {
    return true;
  }
}

bool Sema::CheckOwnedQualTypeAssignment(QualType LHSType, QualType RHSType, SourceLocation RLoc) {
  QualType RHSCanType = RHSType.getCanonicalType();
  QualType LHSCanType = LHSType.getCanonicalType();
  const auto *LHSPtrType = LHSType->getAs<PointerType>();
  const auto *RHSPtrType = RHSType->getAs<PointerType>();
  bool IsPointer = LHSPtrType && RHSPtrType;
  bool IsSameType = (LHSCanType.getTypePtr() == RHSCanType.getTypePtr());
  bool IsTraitImplType = (LHSCanType->isTraitType() || RHSCanType->isTraitType());

  // owned to owned cases:
  // int* owned  <->  int* owned   // legal
  // int* owned  <->  float* owned // illegal
  // const int** owned  <->  int** owned  // legal
  // trait T* owned <- [type : trait T] * owned // legal
  // unOwned to unOwned cases:
  // owned int* owned *  <->  owned int**  // illegal
  // owned int* const *  <->  owned int**  // legal
  if (LHSCanType.isOwnedQualified() == RHSCanType.isOwnedQualified() ||
      (LHSCanType->isTraitType() && RHSCanType->isOwnedStructureType())) {
    if (IsSameType) {
      return true;
    }
    if (IsTraitImplType) {
      return true;
    }
    if (!IsPointer) {
      return false;
    } else {
      // owned struct S* <-> void* //legal
      if (!LHSCanType.isOwnedQualified() && (LHSPtrType->isVoidPointerType() || RHSPtrType->isVoidPointerType()))
        return true;
      return CheckOwnedQualTypeAssignment(LHSPtrType->getPointeeType(), RHSPtrType->getPointeeType(), RLoc);
    }
  }

  // trait T* owned <-> trait T* owned // legal
  if (LHSCanType.isOwnedQualified() || RHSCanType.isOwnedQualified()) {
    TraitDecl *TD = TryDesugarTrait(LHSType);
    if (TD) {
      QualType QT = DesugarTraitToStructTrait(TD, LHSCanType, RLoc);
      if (QT.getCanonicalType() == RHSCanType) {
        return true;
      }
    }
  }

  // unOwned <-> owned
  // int* owned <-> int*  //illegal
  return false;
}

bool Sema::CheckOwnedQualTypeAssignment(QualType LHSType, Expr* RHSExpr) {
  QualType RHSCanType = RHSExpr->getType().getCanonicalType();
  QualType LHSCanType = LHSType.getCanonicalType();
  bool IsLiteral = false;
  Stmt::StmtClass RHSClass = RHSExpr->getStmtClass();
  if (RHSClass == Expr::IntegerLiteralClass
      || RHSClass == Expr::FloatingLiteralClass
      || RHSClass == Expr::CharacterLiteralClass) {
    IsLiteral = true;
  }
  SourceLocation ExprLoc = RHSExpr->getBeginLoc();
  // Owned pointer can be inited by nullptr.
  if (LHSCanType.isOwnedQualified() && LHSCanType->isPointerType() &&
      isa<CXXNullPtrLiteralExpr>(RHSExpr))
    return true;

  bool Res = true;

  // unOwned to owned initialize cases:
  // int owned a = 10;        //legal even 10 is not owned type
  // int owned b = 10 + 10;   //ilegal
  // char owned c = 'c';      // legal even 'c' is int type
  // int owned d = (int)a;    // illegal
  if (LHSCanType.isOwnedQualified() && !RHSCanType.isOwnedQualified() && IsLiteral) {
    if (LHSCanType.getTypePtr() != RHSCanType.getTypePtr()
        && !(LHSCanType.getTypePtr()->isCharType() && RHSCanType.getTypePtr()->isIntegerType())) {
      Res = false;
    }
  } else {
    Res = CheckOwnedQualTypeAssignment(LHSType, RHSCanType, ExprLoc);
  }
  if (!Res) {
    Diag(ExprLoc, diag::err_owned_qualcheck_incompatible) << RHSExpr->getType() << LHSType;
  }
  return Res;
}

bool Sema::CheckOwnedFunctionPointerType(QualType LHSType, Expr* RHSExpr) {
  const FunctionProtoType* LSHFuncType = LHSType->getAs<PointerType>()->getPointeeType()->getAs<FunctionProtoType>();
  const FunctionProtoType* RSHFuncType = RHSExpr->getType()->isFunctionPointerType()?
    RHSExpr->getType()->getAs<PointerType>()->getPointeeType()->getAs<FunctionProtoType>():
    RHSExpr->getType()->getAs<FunctionProtoType>();
  SourceLocation ExprLoc = RHSExpr->getBeginLoc();

  // return if no 'owned' in both side
  if (!LSHFuncType->hasOwnedRetOrParams() && !RSHFuncType->hasOwnedRetOrParams()) {
    return true;
  }
  if ((LSHFuncType->getReturnType().isOwnedQualified() && !RSHFuncType->getReturnType().isOwnedQualified())
       || (!LSHFuncType->getReturnType().isOwnedQualified() && RSHFuncType->getReturnType().isOwnedQualified())) {
    Diag(ExprLoc, diag::err_owned_funcPtr_incompatible) << LHSType << RHSExpr->getType();
    return false;
  }
  if (LSHFuncType->getNumParams() != RSHFuncType->getNumParams()) {
    Diag(ExprLoc, diag::err_owned_funcPtr_incompatible) << LHSType << RHSExpr->getType();
    return false;
  }
  for (unsigned i = 0; i < LSHFuncType->getNumParams(); i++) {
    if ((LSHFuncType->getParamType(i).isOwnedQualified() && !RSHFuncType->getParamType(i).isOwnedQualified())
         || (!LSHFuncType->getParamType(i).isOwnedQualified() && RSHFuncType->getParamType(i).isOwnedQualified())) {
      Diag(ExprLoc, diag::err_owned_funcPtr_incompatible) << LHSType << RHSExpr->getType();
      return false;
    }
  }
  return true;
}

bool Sema::CheckTemporaryVarMemoryLeak(Expr* E) {
  if (!dyn_cast<CallExpr>(E)) return false;
  QualType RetType = E->getType().getCanonicalType();
  if (RetType.isOwnedQualified() || RetType->isMoveSemanticType()) {
    std::string ExprString;
    llvm::raw_string_ostream ExprStream(ExprString);
    E->printPretty(ExprStream, nullptr, clang::PrintingPolicy(getLangOpts()));
    Diag(E->getBeginLoc(), diag::err_owned_temporary_memLeak) << ExprStream.str();
    return true;
  }
  return false;
}

void Sema::CheckMoveVarMemoryLeak(Expr* E, SourceLocation SL) {
  if (E == nullptr)
    return;
  if (auto UO = dyn_cast_or_null<UnaryOperator>(E->IgnoreParenCasts())) {
    if (UO->getOpcode() == UO_Deref && UO->getType().isOwnedQualified()
        && UO->getSubExpr()->getType().isBorrowQualified()) {
        Diag(SL, diag::err_move_borrow);
    }
  } else if (auto ME = dyn_cast_or_null<MemberExpr>(E->IgnoreParenCasts())) {
    if (ME->getType().isOwnedQualified() && ME->getBase()->getType().isBorrowQualified())
      Diag(SL, diag::err_move_borrow);
  }
}

bool Sema::CheckBorrowQualTypeCStyleCast(QualType LHSType, QualType RHSType) {
  QualType RHSCanType = RHSType.getCanonicalType();
  QualType LHSCanType = LHSType.getCanonicalType();
  bool IsSameType = (LHSCanType.getTypePtr() == RHSCanType.getTypePtr());
  const auto *LHSPtrType = LHSType->getAs<PointerType>();
  const auto *RHSPtrType = RHSType->getAs<PointerType>();
  bool IsPointer = LHSPtrType && RHSPtrType;
  QualType RHSRawType = RHSCanType.getUnqualifiedType();
  QualType LHSRawType = LHSCanType.getUnqualifiedType();

  if (IsSameType) {
    return true;
  }
  if (IsPointer) {
    if (LHSCanType->isVoidPointerType()) {
      return true;
    } else if (RHSCanType->isVoidPointerType() && !IsInSafeZone()) {
      return true;
    } else if (Context.hasSameType(LHSRawType, RHSRawType)) {
      return true;
    } else if (TryDesugarTrait(RHSType)) {
      return true;
    } else {
      return CheckBorrowQualTypeCStyleCast(LHSPtrType->getPointeeType(),
                                           RHSPtrType->getPointeeType());
    }
  }
  return false;
}

bool Sema::CheckBorrowQualTypeCStyleCast(QualType LHSType, QualType RHSType, SourceLocation RLoc) {
  if (!CheckBorrowQualTypeCStyleCast(LHSType, RHSType)) {
    Diag(RLoc, diag::err_borrow_qualcheck_incompatible) << CompleteTraitType(RHSType) << CompleteTraitType(LHSType);
    return false;
  } else {
    return true;
  }
}

bool Sema::CheckBorrowQualTypeAssignment(QualType LHSType, QualType RHSType, SourceLocation RLoc) {
  QualType RHSCanType = RHSType.getCanonicalType();
  QualType LHSCanType = LHSType.getCanonicalType();
  const auto *LHSPtrType = LHSType->getAs<PointerType>();
  const auto *RHSPtrType = RHSType->getAs<PointerType>();
  bool IsPointer = LHSPtrType && RHSPtrType;

  if (LHSCanType.isBorrowQualified() == RHSCanType.isBorrowQualified()) {
    if (TraitDecl *TD = TryDesugarTrait(LHSCanType)) {
      if (TD->getTypeImpledVarDecl(RHSCanType->getPointeeType()))
        return true;
    }
    if (Context.hasSameType(LHSCanType, RHSCanType)) {
      return true;
    }
    if (LHSCanType->isVoidPointerType()) {
      if (LHSCanType->getPointeeType().isConstQualified() == RHSCanType->getPointeeType().isConstQualified())
        return true;
    }
    if (!IsPointer) {
      return false;
    } else {
      return CheckBorrowQualTypeAssignment(LHSPtrType->getPointeeType(), RHSPtrType->getPointeeType(), RLoc);
    }
  }

  return false;
}

bool Sema::CheckBorrowQualTypeAssignment(QualType LHSType, Expr* RHSExpr) {
  QualType RHSCanType =
      RHSExpr->getType().getCanonicalType().getUnqualifiedType();
  QualType LHSCanType = LHSType.getCanonicalType().getUnqualifiedType();
  SourceLocation ExprLoc = RHSExpr->getBeginLoc();
  bool Res = true;

  if (LHSCanType.isBorrowQualified() || RHSCanType.isBorrowQualified()) {
    if (TraitDecl *TD = TryDesugarTrait(LHSCanType)) {
      if (RHSCanType->isPointerType()) {
        QualType ImplType = RHSCanType->getPointeeType().getUnqualifiedType().getCanonicalType();
        ImplType.removeLocalOwned();
        if (TD->getTypeImpledVarDecl(ImplType))
          return true;
      }
      // trait T* borrow <-> trait T* borrow // legal
      if (TD) {
        QualType QT = DesugarTraitToStructTrait(TD, LHSCanType, RHSExpr->getExprLoc());
        if (QT.getCanonicalType() == RHSCanType) {
          return true;
        }
      }
    }

    // Borrow pointer can be inited by nullptr.
    if (LHSCanType.isBorrowQualified() && isa<CXXNullPtrLiteralExpr>(RHSExpr))
      return true;

    if (LHSCanType->isVoidPointerType()) {
      if (LHSCanType->getPointeeType().isConstQualified() == RHSCanType->getPointeeType().isConstQualified())
        return true;
    }
    if (!Context.hasSameType(LHSCanType, RHSCanType))
      Res = false;
  } else {
    Res = CheckBorrowQualTypeAssignment(LHSType, RHSCanType, ExprLoc);
  }
  if (!Res) {
    Diag(ExprLoc, diag::err_borrow_qualcheck_incompatible)
        << CompleteTraitType(RHSExpr->getType()) << CompleteTraitType(LHSType);
  }
  return Res;
}

bool Sema::CheckBorrowQualTypeCompare(QualType LHSType, QualType RHSType) {
  QualType RHSCanType = RHSType.getCanonicalType();
  QualType LHSCanType = LHSType.getCanonicalType();
  if (LHSCanType.isBorrowQualified() || RHSCanType.isBorrowQualified()) {
    if (RHSCanType != LHSCanType) {
      return false;
    }
  }
  return true;
}

void Sema::CheckBorrowFunctionType(QualType ReturnTy, SmallVector<QualType, 16> ParamTys, SourceLocation SL) {
  if (ReturnTy.hasBorrow()) {
    bool HasBorrowParam = false;
    for (QualType PT : ParamTys) {
      if (PT.hasBorrow()) {
        HasBorrowParam = true;
        break;
      }
    }
    if (!HasBorrowParam)
      Diag(SL, diag::err_typecheck_borrow_func);
  }
}

bool Sema::CheckBorrowFunctionPointerType(QualType LHSType, Expr *RHSExpr) {
  const FunctionProtoType *LSHFuncType = LHSType->getAs<PointerType>()
                                             ->getPointeeType()
                                             ->getAs<FunctionProtoType>();
  const FunctionProtoType *RSHFuncType =
      RHSExpr->getType()->isFunctionPointerType()
          ? RHSExpr->getType()
                ->getAs<PointerType>()
                ->getPointeeType()
                ->getAs<FunctionProtoType>()
          : RHSExpr->getType()->getAs<FunctionProtoType>();
  SourceLocation ExprLoc = RHSExpr->getBeginLoc();

  // return if no 'borrow' in both side
  if (!LSHFuncType->hasBorrowRetOrParams() &&
      !RSHFuncType->hasBorrowRetOrParams()) {
    return true;
  }
  if (!Context.hasSameType(LSHFuncType, RSHFuncType)) {
    Diag(ExprLoc, diag::err_funcPtr_incompatible)
        << LHSType << RHSExpr->getType();
    return false;
  }
  return true;
}

// for global borrow variable type check
void Sema::CheckBorrowOrIndirectBorrowType(SourceLocation ErrLoc, QualType T,
                                           StringRef Env) {
  enum { BorrowQualified, BorrowTypedef, BorrowFields };
  if (T.getCanonicalType().isBorrowQualified() &&
      !T.getTypePtr()->getAs<TypedefType>()) {
    Diag(ErrLoc, diag::err_owned_inderictOwned_type_check)
        << BorrowQualified << "borrow" << Env;
  } else if (T.getCanonicalType().isBorrowQualified() &&
             T.getTypePtr()->getAs<TypedefType>()) {
    Diag(ErrLoc, diag::err_owned_inderictOwned_type_check)
        << BorrowTypedef << "borrow" << Env << T;
  } else if (T.getCanonicalType().getTypePtr()->hasBorrowFields()) {
    Diag(ErrLoc, diag::err_owned_inderictOwned_type_check)
        << BorrowFields << "borrow" << Env << T;
  }
}
#endif
