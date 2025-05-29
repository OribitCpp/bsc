//===- TypeBSC.cpp - Type representation and manipulation -----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file implements the BSC type-related functionality.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/AST/Decl.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Type.h"

using namespace clang;

// hasOwnedFields is used to determine whether a type has a field
// that is directly or indirectly qualified by owned.
// If you want to determine whether a type is a move semantic type,
// use isMoveSemanticType instead.
bool PointerType::hasOwnedFields() const {
  QualType R = getPointeeType();
  if (R.isOwnedQualified()) {
    return true;
  }
  if (R.getTypePtr()->hasOwnedFields()) {
    return true;
  }
  return false;
}

// hasOwnedFields is used to determine whether a type has a field
// that is directly or indirectly qualified by owned.
// If you want to determine whether a type is a move semantic type,
// use isMoveSemanticType instead.
bool Type::hasOwnedFields() const {
  if (const auto *RecTy = dyn_cast<RecordType>(CanonicalType)) {
    return RecTy->hasOwnedFields();
  } else if (const auto *PointerTy = dyn_cast<PointerType>(CanonicalType)) {
    return PointerTy->hasOwnedFields();
  }
  return false;
}

bool PointerType::hasBorrowFields() const {
  QualType R = getPointeeType();
  if (R.isBorrowQualified()) {
    return true;
  }
  if (R.getTypePtr()->hasBorrowFields()) {
    return true;
  }
  return false;
}

bool Type::hasBorrowFields() const {
  if (const auto *RecTy = dyn_cast<RecordType>(CanonicalType)) {
    return RecTy->hasBorrowFields();
  } else if (const auto *PointerTy = dyn_cast<PointerType>(CanonicalType)) {
    return PointerTy->hasBorrowFields();
  }
  return false;
}

bool Type::withBorrowFields() const {
  if (const auto *RT = dyn_cast<RecordType>(CanonicalType)) {
    return RT->withBorrowFields();
  }
  return false;
}

bool FunctionProtoType::hasOwnedRetOrParams() const {
  if (getReturnType().isOwnedQualified()) {
    return true;
  }
  for (auto ParamType : getParamTypes()) {
    if (ParamType.isOwnedQualified()) {
      return true;
    }
  }
  return false;
}

bool FunctionProtoType::hasBorrowRetOrParams() const {
  if (getReturnType().hasBorrow()) {
    return true;
  }
  for (auto ParamType : getParamTypes()) {
    if (ParamType.hasBorrow()) {
      return true;
    }
  }
  return false;
}

bool Type::checkFunctionProtoType(SafeZoneSpecifier SZS) const {
  const FunctionProtoType *FPT = nullptr;
  if (isFunctionType()) {
    FPT = getAs<FunctionProtoType>();
  } else if (isFunctionPointerType()) {
    FPT = getPointeeType()->getAs<FunctionProtoType>();
  }
  if (FPT) {
    FunctionProtoType::ExtProtoInfo EPI = FPT->getExtProtoInfo();
    return EPI.SafeZoneSpec == SZS;
  }
  return false;
}

bool Type::isOwnedStructureType() const {
  if (const auto *RT = getAs<RecordType>())
    return RT->getDecl()->isStruct() && RT->getDecl()->isOwnedDecl();
  return false;
}

bool Type::isOwnedTemplateSpecializationType() const {
  if (const auto *RT = getAs<TemplateSpecializationType>()) {
    if (RT->getTemplateName().getAsTemplateDecl() &&
        RT->getTemplateName().getAsTemplateDecl()->getTemplatedDecl()) {
      if (auto RD = dyn_cast<RecordDecl>(
              RT->getTemplateName().getAsTemplateDecl()->getTemplatedDecl()))
        return RD->isOwnedDecl();
    }
  }
  return false;
}

// Return true when a type is move semantic type,
// including owned pointer(int *owned, int **owned, ...),
// owned struct and struct which has owned fields, for example:
// @code
//     owned struct S1 { };
//     struct S2 { int* owned p; };
//     struct S3 { S1 s; };
//     struct S4 { struct S2 s; };
// @endcode
// These types are not move semantic:
// @code
//     struct S5 { S1* s};
//     struct S6 { int *owned * p};
// @endcode
bool Type::isMoveSemanticType() const {
  // Owned pointer or owned struct is owned qualified.
  if (CanonicalType.isOwnedQualified())
    return true;
  if (const auto *RecTy = dyn_cast<RecordType>(CanonicalType)) {
    if (RecordDecl *RD = RecTy->getDecl()) {
      for (FieldDecl *FD : RD->fields()) {
        QualType FQT = FD->getType().getCanonicalType();
        if (FQT.isOwnedQualified())
          return true;
        else if (isa<RecordType>(FQT))
          return FQT->isMoveSemanticType();
      }
    }
  }
  return false;
}

void RecordType::initOwnedStatus() const {
  if (hasOwn != ownedStatus::unInitOwned)
    return;
  std::vector<const RecordType *> RecordTypeList;
  RecordTypeList.push_back(this);
  unsigned NextToCheckIndex = 0;

  while (RecordTypeList.size() > NextToCheckIndex) {
    for (FieldDecl *FD :
         RecordTypeList[NextToCheckIndex]->getDecl()->fields()) {
      QualType FieldTy = FD->getType().getCanonicalType();
      bool isOwnedStructType = FieldTy->isOwnedStructureType();
      if (FieldTy.isOwnedQualified() || isOwnedStructType) {
        hasOwn = ownedStatus::withOwned;
        return;
      }
      QualType tempQT = FieldTy;
      const Type *tempT = tempQT.getTypePtr();
      while (tempT->isPointerType()) {
        tempQT = tempT->getPointeeType();
        isOwnedStructType = tempQT.getCanonicalType()->isOwnedStructureType();
        if (tempQT.isOwnedQualified() && !isOwnedStructType) {
          hasOwn = ownedStatus::withOwned;
          return;
        } else {
          tempQT = tempQT.getCanonicalType();
          tempT = tempQT.getTypePtr();
        }
      }
      FieldTy = tempQT.getCanonicalType();
      if (const auto *FieldRecTy = FieldTy->getAs<RecordType>()) {
        if (llvm::find(RecordTypeList, FieldRecTy) == RecordTypeList.end())
          RecordTypeList.push_back(FieldRecTy);
      }
    }
    ++NextToCheckIndex;
  }
  hasOwn = ownedStatus::withoutOwned;
  return;
}

// hasOwnedFields is used to determine whether a type has a field
// that is directly or indirectly qualified by owned.
// If you want to determine whether a type is a move semantic type,
// use isMoveSemanticType instead.
bool RecordType::hasOwnedFields() const {
  if (hasOwn == ownedStatus::unInitOwned)
    initOwnedStatus();
  if (hasOwn == ownedStatus::withOwned)
    return true;
  return false;
}

void RecordType::initBorrowStatus() const {
  if (hasBorrow != borrowStatus::unInitBorrow)
    return;
  std::vector<const RecordType *> RecordTypeList;
  RecordTypeList.push_back(this);
  unsigned NextToCheckIndex = 0;

  while (RecordTypeList.size() > NextToCheckIndex) {
    for (FieldDecl *FD :
         RecordTypeList[NextToCheckIndex]->getDecl()->fields()) {
      QualType FieldTy = FD->getType();
      if (FieldTy.isBorrowQualified()) {
        hasBorrow = borrowStatus::withBorrow;
        return;
      }
      QualType tempQT = FieldTy;
      const Type *tempT = tempQT.getTypePtr();
      while (tempT->isPointerType()) {
        tempQT = tempT->getPointeeType();
        if (tempQT.isBorrowQualified()) {
          hasBorrow = borrowStatus::withBorrow;
          return;
        } else {
          tempQT = tempQT.getCanonicalType();
          tempT = tempQT.getTypePtr();
        }
      }
      FieldTy = tempQT.getCanonicalType();
      if (const auto *FieldRecTy = FieldTy->getAs<RecordType>()) {
        if (llvm::find(RecordTypeList, FieldRecTy) == RecordTypeList.end())
          RecordTypeList.push_back(FieldRecTy);
      }
    }
    ++NextToCheckIndex;
  }
  hasBorrow = borrowStatus::withoutBorrow;
  return;
}

bool RecordType::hasBorrowFields() const {
  if (hasBorrow == borrowStatus::unInitBorrow)
    initBorrowStatus();
  if (hasBorrow == borrowStatus::withBorrow)
    return true;
  return false;
}

bool RecordType::withBorrowFields() const {
  std::vector<const RecordType*> RecordTypeList;
  RecordTypeList.push_back(this);
  unsigned NextToCheckIndex = 0;

  while (RecordTypeList.size() > NextToCheckIndex) {
    for (FieldDecl *FD :
         RecordTypeList[NextToCheckIndex]->getDecl()->fields()) {
      QualType FieldTy = FD->getType();
      if (FieldTy.isBorrowQualified())
        return true;
      FieldTy = FieldTy.getCanonicalType();
      if (const auto *FieldRecTy = FieldTy->getAs<RecordType>()) {
        if (!llvm::is_contained(RecordTypeList, FieldRecTy))
          RecordTypeList.push_back(FieldRecTy);
      }
    }
    ++NextToCheckIndex;
  }
  return false;
}

bool Type::isBSCFutureType() const {
  if (const auto *RT = getAs<RecordType>()) {
    RecordDecl *RD = RT->getAsRecordDecl();
    if (isa<ClassTemplateSpecializationDecl>(RD)) {
      return RD->getNameAsString() == "__Trait_Future";
    }
  }
  return false;
}

ConditionalType::ConditionalType(llvm::Optional<bool> CondRes, Expr *CondE,
                                 QualType T1, QualType T2, QualType can)
    : Type(Conditional, can,
           toTypeDependence(CondE->getDependence()) |
               (CondE->isInstantiationDependent() ? TypeDependence::Dependent
                                                  : TypeDependence::None) |
               (CondE->getType()->getDependence() &
                TypeDependence::VariablyModified) |
               T1->getDependence() | T2->getDependence()),
      CondResult(CondRes), CondExpr(CondE), Type1(T1), Type2(T2),
      UnderlyingType(can) {}

bool ConditionalType::isSugared() const {
  return !CondExpr->isInstantiationDependent();
}

QualType ConditionalType::desugar() const {
  if (isSugared())
    return getUnderlyingType();

  return QualType(this, 0);
}
bool QualType::hasBorrow() const {
  if (isBorrowQualified())
    return true;
  return getTypePtr()->hasBorrowFields();
}

bool QualType::isConstBorrow() const {
  QualType QT = QualType(getTypePtr(), getLocalFastQualifiers());
  if (QT.isLocalBorrowQualified()) {
    while (QT->isPointerType()) {
      QT = QT->getPointeeType();
    }
    if (QT.isLocalConstQualified())
      return true;
  }
  return false;
}

bool QualType::isConstPointee() const {
  QualType QT = QualType(getTypePtr(), getLocalFastQualifiers());
  while (QT->isPointerType()) {
      QT = QT->getPointeeType();
  }
  if (QT.isLocalConstQualified())
      return true;
  return false;
}

QualType QualType::addConstBorrow(const ASTContext &Context) {
  SmallVector<unsigned, 4> Qualifiers;
  int PointerNum = 0;
  QualType QT = QualType(getTypePtr(), getLocalFastQualifiers());
  while (QT->isPointerType()) {
    Qualifiers.push_back(QT.getLocalFastQualifiers());
    QT = QT->getPointeeType();
    PointerNum++;
  }
  QT.addConst();
  while (PointerNum) {
    QT = Context.getPointerType(QT);
    QT.setLocalFastQualifiers(Qualifiers[PointerNum - 1]);
    PointerNum--;
  }
  QT.addBorrow();
  return QT;
}

QualType QualType::removeConstForBorrow(const ASTContext &Context) {
  SmallVector<unsigned, 4> Qualifiers;
  int PointerNum = 0;
  QualType QT = QualType(getTypePtr(), getLocalFastQualifiers());
  while (QT->isPointerType()) {
    Qualifiers.push_back(QT.getLocalFastQualifiers());
    QT = QT->getPointeeType();
    PointerNum++;
  }
  QT.removeLocalConst();
  PointerNum--;
  while (PointerNum + 1) {
    QT = Context.getPointerType(QT);
    QT.setLocalFastQualifiers(Qualifiers[PointerNum]);
    PointerNum--;
  }
  return QT;
}

#endif