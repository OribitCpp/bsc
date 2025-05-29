//===--- SemaBSCSafeZone.cpp - Semantic Analysis for BSC safe zone ------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements semantic analysis for BSC safe zone
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC
#include "clang/AST/Type.h"
#include "clang/Sema/ScopeInfo.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/SemaDiagnostic.h"
#include "clang/Sema/Template.h"
#include "llvm/ADT/SmallVector.h"

using namespace clang;
using namespace sema;

bool Sema::IsInSafeZone() {
  if (!getLangOpts().BSC) {
    return false;
  }
  if (CurrentInstantiationScope) {
    return getInstantiationSafeZoneSpecifier() == SZ_Safe;
  } else {
    return getCurScope()->getScopeSafeZoneSpecifier() == SZ_Safe;
  }
}

bool Sema::IsSafeFunctionPointerType(QualType Type) {
  if (Type->isFunctionPointerType()) {
    const FunctionProtoType *LSHFuncType =
        Type->getPointeeType()->getAs<FunctionProtoType>();
    if (LSHFuncType && LSHFuncType->getFunSafeZoneSpecifier() == SZ_Safe) {
      return true;
    }
  }
  return false;
}

// Allow or not allow base-type conversion in the safe zone
// 0:void; 1:_Bool; 2:unsigned char; 3:unsigned short; 4: unsigned int;
// 5:unsigned long 6:unsigned long long; 7:char; 8:short; 9:int; 10:long;
// 11:long long; 12 float 13:double; 14:long double;
// sourceType | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10| 11| 12| 13| 14|
// ------------------------------------------------------------------------
// destType.0 | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y |
// .........1 | N | Y | N | N | N | N | N | N | N | N | N | N | N | N | N |
// .........2 | N | Y | Y | N | N | N | N | N | N | N | N | N | N | N | N |
// .........3 | N | Y | Y | Y | N | N | N | N | N | N | N | N | N | N | N |
// .........4 | N | Y | Y | Y | Y | N | N | N | N | N | N | N | N | N | N |
// .........5 | N | Y | Y | Y | Y | Y | N | N | N | N | N | N | N | N | N |
// .........6 | N | Y | Y | Y | Y | Y | Y | N | N | N | N | N | N | N | N |
// .........7 | N | Y | N | N | N | N | N | Y | N | N | N | N | N | N | N |
// .........8 | N | Y | Y | N | N | N | N | Y | Y | N | N | N | N | N | N |
// .........9 | N | Y | Y | Y | N | N | N | Y | Y | Y | N | N | N | N | N |
// ........10 | N | Y | Y | Y | N | N | N | Y | Y | Y | Y | N | N | N | N |
// ........11 | N | Y | Y | Y | Y | Y | N | Y | Y | Y | Y | Y | N | N | N |
// ........12 | N | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | N | N |
// ........13 | N | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | N |
// ........14 | N | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y | Y |

bool Sema::IsSafeBuiltinTypeConversion(BuiltinType::Kind SourceType,
                                       BuiltinType::Kind DestType) {
  static const std::map<BuiltinType::Kind, int> SafeZoneMap = {
      {BuiltinType::Void, 0},       {BuiltinType::Bool, 1},
      {BuiltinType::Char_U, 2},     {BuiltinType::UChar, 2},
      {BuiltinType::UShort, 3},     {BuiltinType::UInt, 4},
      {BuiltinType::ULong, 5},      {BuiltinType::ULongLong, 6},
      {BuiltinType::SChar, 7},      {BuiltinType::Char_S, 7},
      {BuiltinType::Short, 8},      {BuiltinType::Int, 9},
      {BuiltinType::Long, 10},      {BuiltinType::LongLong, 11},
      {BuiltinType::Float, 12},     {BuiltinType::Double, 13},
      {BuiltinType::LongDouble, 14}};
  bool Y = true;
  bool N = false;

  static const bool EnableToConvert[15][15] = {
      {Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y},
      {N, Y, N, N, N, N, N, N, N, N, N, N, N, N, N},
      {N, Y, Y, N, N, N, N, N, N, N, N, N, N, N, N},
      {N, Y, Y, Y, N, N, N, N, N, N, N, N, N, N, N},
      {N, Y, Y, Y, Y, N, N, N, N, N, N, N, N, N, N},
      {N, Y, Y, Y, Y, Y, N, N, N, N, N, N, N, N, N},
      {N, Y, Y, Y, Y, Y, Y, N, N, N, N, N, N, N, N},
      {N, Y, N, N, N, N, N, Y, N, N, N, N, N, N, N},
      {N, Y, Y, N, N, N, N, Y, Y, N, N, N, N, N, N},
      {N, Y, Y, Y, N, N, N, Y, Y, Y, N, N, N, N, N},
      {N, Y, Y, Y, N, N, N, Y, Y, Y, Y, N, N, N, N},
      {N, Y, Y, Y, Y, Y, N, Y, Y, Y, Y, Y, N, N, N},
      {N, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, N, N},
      {N, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, N},
      {N, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y, Y},
  };

  auto ItSource = SafeZoneMap.find(SourceType);
  auto ItDest = SafeZoneMap.find(DestType);
  if (ItSource != SafeZoneMap.end() && ItDest != SafeZoneMap.end()) {
    return EnableToConvert[ItDest->second][ItSource->second];
  }
  return false;
}

bool Sema::IsSafeConstantValueConversion(QualType DestType, Expr *Expr) {
  QualType SrcType = Expr->getType();
  if (SrcType->isIntegralType(Context) && DestType->isIntegralType(Context)) {
    QualType IntTy = Expr->getType().getUnqualifiedType();
    Expr::EvalResult EVResult;
    bool CstInt = Expr->EvaluateAsInt(EVResult, Context);
    bool IntSigned = IntTy->hasSignedIntegerRepresentation();
    bool OtherIntSigned = DestType->hasSignedIntegerRepresentation();

    if (CstInt) {
      llvm::APSInt Result = EVResult.Val.getInt();
      unsigned NumBits = IntSigned
                             ? (Result.isNegative() ? Result.getMinSignedBits()
                                                    : Result.getActiveBits())
                             : Result.getActiveBits();

      if (Result.isNegative()) {
        if (OtherIntSigned) {
          // source is negative number, destination is signed type
          return Context.getIntWidth(DestType) >= NumBits;
        } else {
          // source is negative number, destination is unsigned type
          return false;
        }
      } else {
        if (OtherIntSigned) {
          // source is positive number, destination is signed type
          return Context.getIntWidth(DestType) > NumBits;
        } else {
          // source is positive number, destination is unsigned type
          return Context.getIntWidth(DestType) >= NumBits;
        }
      }
    }
  }
  if (DestType->isRealFloatingType()) {
    if (SrcType->isRealFloatingType() && !Expr->isValueDependent()) {
      // lose of the precision conversion is not allowed
      llvm::APFloat Result(0.0);
      bool CstFloat = Expr->EvaluateAsFloat(Result, Context);
      if (CstFloat) {
        bool Truncated = true;
        Result.convert(Context.getFloatTypeSemantics(DestType),
                       llvm::APFloat::rmNearestTiesToEven, &Truncated);
        if (!Truncated)
          return true;
      }
    }
  }

  return false;
}

bool Sema::IsSafeFunctionPointerTypeCast(QualType DestType, Expr *SrcExpr) {
  if (!DestType->isFunctionPointerType()) {
    return true;
  }
  if (!SrcExpr->getType()->isFunctionPointerType() &&
      !SrcExpr->getType()->isFunctionType()) {
    return true;
  }
  // bsc desugar cast expression is a safe conversion.
  if (SrcExpr->IsDesugaredCastExpr) {
    return true;
  }
  const FunctionProtoType *LSHFuncType = DestType->getAs<PointerType>()
                                             ->getPointeeType()
                                             ->getAs<FunctionProtoType>();
  const FunctionProtoType *RSHFuncType =
      SrcExpr->getType()->isFunctionPointerType()
          ? SrcExpr->getType()
                ->getAs<PointerType>()
                ->getPointeeType()
                ->getAs<FunctionProtoType>()
          : SrcExpr->getType()->getAs<FunctionProtoType>();
  // conversion to an unsafe type is allowed in the unsafe zone
  // only need to care about the safe zone or safe type
  if (!IsInSafeZone() && LSHFuncType->getFunSafeZoneSpecifier() != SZ_Safe) {
    return true;
  }

  if ((LSHFuncType->getFunSafeZoneSpecifier() !=
       RSHFuncType->getFunSafeZoneSpecifier()) &&
      (LSHFuncType->getFunSafeZoneSpecifier() == SZ_Safe ||
       RSHFuncType->getFunSafeZoneSpecifier() == SZ_Safe)) {
    Diag(SrcExpr->getBeginLoc(), diag::err_unsafe_fun_cast)
        << SrcExpr->getType() << DestType;
    return false;
  }

  if (LSHFuncType->getReturnType().getUnqualifiedType() !=
      RSHFuncType->getReturnType().getUnqualifiedType()) {
    Diag(SrcExpr->getBeginLoc(), diag::err_unsafe_fun_cast)
        << SrcExpr->getType() << DestType;
    return false;
  }

  if (LSHFuncType->getNumParams() != RSHFuncType->getNumParams()) {
    Diag(SrcExpr->getBeginLoc(), diag::err_unsafe_fun_cast)
        << SrcExpr->getType() << DestType;
    return false;
  }

  for (unsigned i = 0; i < LSHFuncType->getNumParams(); i++) {
    if (LSHFuncType->getParamType(i).getUnqualifiedType() !=
        RSHFuncType->getParamType(i).getUnqualifiedType()) {
      Diag(SrcExpr->getBeginLoc(), diag::err_unsafe_fun_cast)
          << SrcExpr->getType() << DestType;
      return false;
    }
  }

  return true;
}

bool Sema::IsSafeConversion(QualType DestType, Expr *Expr) {
  // check function pointer Type in 'IsSafeFunctionPointerTypeCast'
  if (DestType->isFunctionPointerType()) {
    return true;
  }
  // only check in the safe zone
  if (!IsInSafeZone()) {
    return true;
  }

  // Init a owned or borrow pointer by nullptr is allowed in the safe zone
  if ((DestType.isOwnedQualified() && DestType->isPointerType()) ||
      DestType.isBorrowQualified()) {
    if (isa<CXXNullPtrLiteralExpr>(Expr))
      return true;
  }

  bool IsSafeBehavior = true;
  QualType SrcType = Expr->getType();
  if (IsTraitExpr(Expr)) {
    SrcType = CompleteTraitType(SrcType);
  }
  // conversion from non trait pointer type to trait pointer type is allowed
  if (DestType->isTraitPointerType() && !SrcType->isTraitPointerType()) {
    return true;
  }
  if (const ConditionalOperator *Exp = dyn_cast<ConditionalOperator>(Expr)) {
    if (IsSafeConversion(DestType, Exp->getTrueExpr())) {
      return IsSafeConversion(DestType, Exp->getFalseExpr());
    } else {
      return false;
    }
  } else if (SrcType->isPointerType() && DestType->isPointerType()) {
    // different pointer type does not allow conversion, except for conversion
    // from owned pointer to `void* owned`
    if (SrcType.getCanonicalType() != DestType.getCanonicalType()) {
      if (SrcType.getCanonicalType().isOwnedQualified() &&
          DestType.getCanonicalType()->isVoidPointerType() &&
          DestType.getCanonicalType().isOwnedQualified())
        IsSafeBehavior = true;
      else
        IsSafeBehavior = false;
    }
  } else if (SrcType->isPointerType() || DestType->isPointerType()) {
    // conversion from pointer to non-pointer or non-pointer to pointer is not
    // allowed
    IsSafeBehavior = false;
  } else {
    const auto *SBT =
        dyn_cast<BuiltinType>(SrcType->getUnqualifiedDesugaredType());
    const auto *DBT =
        dyn_cast<BuiltinType>(DestType->getUnqualifiedDesugaredType());
    if (SBT && DBT) {
      if (SBT->getKind() != DBT->getKind()) {
        // conversion from high-precision to low-precision is not allowed
        // conversion from wide range to narrow range is not allowed
        if (!IsSafeBuiltinTypeConversion(SBT->getKind(), DBT->getKind())) {
          IsSafeBehavior = false;
        }
      }
    }
    // conversion const value is allowed, if the destination type can embrace it
    if (!DestType->isEnumeralType() && !SrcType->isEnumeralType() &&
        IsSafeConstantValueConversion(DestType, Expr)) {
      IsSafeBehavior = true;
    }

    if (DestType->isEnumeralType() || SrcType->isEnumeralType()) {
      IsSafeBehavior = false;
      // conversion different enum type is not allowed
      if (SrcType.getCanonicalType() == DestType.getCanonicalType()) {
        IsSafeBehavior = true;
        // conversion enum value type to enum variable type is allowed
      } else if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(Expr)) {
        if (EnumConstantDecl *ECD =
                dyn_cast<EnumConstantDecl>(DRE->getDecl())) {
          EnumDecl *Enum = cast<EnumDecl>(ECD->getDeclContext());
          SrcType = Context.getTypeDeclType(Enum);
          if (DestType.getCanonicalType() == SrcType.getCanonicalType()) {
            IsSafeBehavior = true;
          }
        }
      }
    }
  }

  if (!IsSafeBehavior) {
    Diag(Expr->getExprLoc(), diag::err_unsafe_cast) << SrcType << DestType;
  }
  return IsSafeBehavior;
}

bool Sema::IsUnsafeType(QualType Type) {
  if (Type.isNull()) {
    return false;
  }
  if (Type->isPointerType() && !Type->isFunctionPointerType() &&
      !(Type.isOwnedQualified() || Type.isBorrowQualified())) {
    return true;
  }
  if (Type->isUnionType()) {
    return true;
  }
  if (Type->isOwnedStructureType()) {
    return false;
  }
  if (Type->isStructureType()) {
    if (const auto *RT = Type->getAs<RecordType>()) {
      RecordDecl *RD = RT->getDecl();
      for (RecordDecl::field_iterator i = RD->field_begin(),
                                      e = RD->field_end();
           i != e; ++i) {
        if (IsUnsafeType(i->getType())) {
          return true;
        }
      }
    }
  }
  if (Type->isArrayType()) {
    return IsUnsafeType(cast<ArrayType>(Type)->getElementType());
  }
  return false;
}

void Sema::DiagnoseInvalidMemberAccessExprInSafeZone(SourceLocation OpLoc,
                                                     tok::TokenKind Kind,
                                                     QualType T) {
  if (!IsInSafeZone())
    return;

  switch (Kind) {
  case tok::arrow: {
    if (!T.isNull() && T->isPointerType() &&
        !(T.getCanonicalType().isOwnedQualified() || T.getCanonicalType().isBorrowQualified()))
      Diag(OpLoc, diag::err_unsafe_action)
          << "'->' operator used by raw pointer type";
    break;
  }
  case tok::period: {
    if (!T.isNull() && T->isUnionType())
      Diag(OpLoc, diag::err_unsafe_action) << "'.' operator used by union type";
    break;
  }
  default:
    break;
  }
}

void Sema::DiagnoseInvalidUnaryExprInSafeZone(SourceLocation OpLoc,
                                              UnaryOperatorKind Opc,
                                              QualType T) {
  if (!IsInSafeZone())
    return;

  switch (Opc) {
  case UO_PreInc:
  case UO_PostInc:
    Diag(OpLoc, diag::err_unsafe_action) << "'++' operator";
    break;
  case UO_PreDec:
  case UO_PostDec:
    Diag(OpLoc, diag::err_unsafe_action) << "'--' operator";
    break;
  case UO_AddrOf: {
    if (T.isNull() || !T->isFunctionType()) {
      Diag(OpLoc, diag::err_unsafe_action) << "'&' operator";
    }
    break;
  }
  case UO_Deref: {
    if (!T.isNull() && T->isPointerType() &&
        !T.getCanonicalType().isOwnedQualified() &&
        !T.getCanonicalType().isBorrowQualified())
      Diag(OpLoc, diag::err_unsafe_action) << "'*' operator";
    break;
  }
  default:
    break;
  }
}

void Sema::DiagnoseIncompleteInitStructTypeInSafeZone(InitListExpr *IList) {
  // allow initialization by '{0}' and '{}'.
  bool IsInitToZero = false;
  if (IList->getNumInits() == 1) {
    Expr *Init = IList->getInit(0);
    if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(Init))
      Init = ICE->getSubExpr();
    if (const auto *IL = dyn_cast<IntegerLiteral>(Init)) {
      IsInitToZero = IL->getValue().isZero();
    }
  } else if (IList->getNumInits() == 0) {
    IsInitToZero = true;
  }

  if (!IsInitToZero) {
    Diag(IList->getBeginLoc(), diag::err_unsafe_action)
        << "incomplete initialization";
  }
}

void Sema::PushInsSafeZone(SafeZoneSpecifier SafeZoneSpec) {
  getCurFunction()->InsCompoundSafeZone.push_back(
      InsCompoundSafeZoneInfo(SafeZoneSpec));
}

void Sema::PopInsSafeZone() {
  FunctionScopeInfo *CurFunction = getCurFunction();
  assert(!CurFunction->InsCompoundSafeZone.empty() && "mismatched push/pop");

  CurFunction->InsCompoundSafeZone.pop_back();
}

sema::InsCompoundSafeZoneInfo &Sema::getCurInsCompoundSafeZone() const {
  return getCurFunction()->InsCompoundSafeZone.back();
}

SafeZoneSpecifier Sema::getInstantiationSafeZoneSpecifier() {
  SafeZoneSpecifier SafeZoneSpec = SZ_None;
  if (getCurFunction()) {
    if (getCurFunction()->InsCompoundSafeZone.size() == 0) {
      if (CurrentInstantiationScope)
        SafeZoneSpec = CurrentInstantiationScope->getScopeSafeZoneSpecifier();
    } else {
      SafeZoneSpec =
          getCurInsCompoundSafeZone().getInsCompoundSafeZoneSpecifier();
    }
  }
  return SafeZoneSpec;
}
#endif
