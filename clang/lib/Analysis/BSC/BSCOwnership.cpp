//===- BSCOwnership.cpp - Ownership Analysis for Source CFGs -*- BSC --*------//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements BSC Ownership analysis for source-level CFGs.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/Analysis/Analyses/BSC/BSCOwnership.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CFG.h"
#include "clang/Analysis/FlowSensitive/DataflowWorklist.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"

using namespace clang;
using namespace std;

namespace {
class OwnershipImpl {
public:
  AnalysisDeclContext &analysisContext;
  ASTContext &ctx;
  llvm::DenseMap<const CFGBlock *, Ownership::OwnershipStatus>
      blocksBeginStatus;
  llvm::DenseMap<const CFGBlock *, Ownership::OwnershipStatus> blocksEndStatus;

  Ownership::OwnershipStatus merge(Ownership::OwnershipStatus statsA,
                                   Ownership::OwnershipStatus statsB);

  Ownership::OwnershipStatus runOnBlock(const CFGBlock *block,
                                        Ownership::OwnershipStatus status,
                                        OwnershipDiagReporter &reporter);

  void MaybeSetNull(const CFGBlock *block, Ownership::OwnershipStatus &status);

  OwnershipImpl(AnalysisDeclContext &ac, ASTContext &context)
      : analysisContext(ac), ctx(context), blocksBeginStatus(0), blocksEndStatus(0) {}
};
} // namespace

//===----------------------------------------------------------------------===//
// Common static functions.
//===----------------------------------------------------------------------===//

static bool IsCallExpr(Expr *E) {
  if (isa<CallExpr>(E))
    return true;

  if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(E)) {
    return isa<CallExpr>(ICE->getSubExpr());
  }
  return false;
}

// IsTrackedType judges if the status of a variable needs to be tracked.
// We track 3 kind of variable according to its type:
// 1. the basic owned pointer type such as `int * owned p`
// 2. the struct owned pointer type such as `struct S * owned s`
// 3. the struct type with at least one owned field
static bool IsTrackedType(QualType type) {
  // case 1 and case 2
  if (type->isPointerType() && type.isOwnedQualified())
    return true;

  // case 3
  if ((type->isRecordType() && type.getTypePtr()->isOwnedStructureType()) ||
      (type->isRecordType() && type->isMoveSemanticType()))
    return true;

  return false;
}

static llvm::SmallSet<string, 10>
findPrefixStrings(const llvm::SmallSet<string, 10> fieldSet, string prefix) {
  llvm::SmallSet<string, 10> prefixStrings = {};
  for (const auto &str : fieldSet) {
    if (str.compare(0, prefix.size(), prefix) == 0) {
      prefixStrings.insert(str);
    }
  }
  return prefixStrings;
}

static unsigned getIndex(Ownership::Status S) {
  int value = static_cast<int>(S);
  unsigned bitIndex = 0;
  while ((value & 1) == 0) {
    value = value >> 1;
    bitIndex++;
  }
  return bitIndex;
}

static pair<const Expr *, string> getMemberFullField(const MemberExpr *ME) {
  const Expr *base = ME->getBase();
  string memberFieldName = ME->getMemberNameInfo().getAsString();

  while (true) {
    if (const MemberExpr *me = dyn_cast<MemberExpr>(base)) {
      memberFieldName =
          me->getMemberNameInfo().getAsString() + "." + memberFieldName;
      base = me->getBase();
    } else if (const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(base)) {
      base = ice->getSubExpr();
    } else {
      break;
    }
  }

  return {base, memberFieldName};
}

static string moveAsterisksToFront(string str) {
  size_t asterisk_pos = str.find_last_not_of('*');
  if (asterisk_pos != string::npos) {
    string asterisks = str.substr(asterisk_pos + 1);
    str.erase(asterisk_pos + 1);
    str.insert(0, asterisks);
  }
  return str;
}

static string concatFields(const VarDecl *VD,
                           llvm::SmallSet<string, 10> fields) {
  string contactedFields = "";
  size_t count = 0;
  for (const string &element : fields) {
    if (count++ != 0) {
      contactedFields += ", ";
    }
    if (VD->getType()->isPointerType() &&
        !VD->getType()->getPointeeType().getCanonicalType()->isRecordType()) {
      contactedFields = contactedFields + element + VD->getNameAsString();
    } else {
      contactedFields =
          contactedFields +
          moveAsterisksToFront(VD->getNameAsString() + "." + element);
    }
    if (count > 8) {
      break;
    }
  }
  if (count == 0) {
    contactedFields += "*" + VD->getNameAsString();
  }
  if (count < fields.size()) {
    contactedFields += "...";
  }
  if (count > 1) {
    contactedFields += " are";
  } else {
    contactedFields += " is";
  }
  return contactedFields;
}

//===----------------------------------------------------------------------===//
// Operations and queries on OwnershipStatus.
//===----------------------------------------------------------------------===//

bool Ownership::OwnershipStatus::empty() const {
  return OPSStatus.empty() && OPSAllOwnedFields.empty() &&
         OPSOwnedOwnedFields.empty() && SStatus.empty() &&
         SAllOwnedFields.empty() && SOwnedOwnedFields.empty() &&
         SNullOwnedFields.empty() && BOPStatus.empty() &&
         BOPAllOwnedFields.empty() && BOPOwnedOwnedFields.empty();
}

Ownership::OwnershipStatus
OwnershipImpl::merge(Ownership::OwnershipStatus statsA,
                     Ownership::OwnershipStatus statsB) {
  if (statsA.empty())
    return Ownership::OwnershipStatus(
        statsB.OPSStatus, statsB.OPSAllOwnedFields, statsB.OPSOwnedOwnedFields,
        statsB.SStatus, statsB.SAllOwnedFields, statsB.SOwnedOwnedFields,
        statsB.SNullOwnedFields,
        statsB.BOPStatus, statsB.BOPAllOwnedFields, statsB.BOPOwnedOwnedFields);

  for (auto it = statsB.OPSStatus.begin(), ei = statsB.OPSStatus.end();
       it != ei; ++it) {
    const VarDecl *VD = it->first;
    const llvm::BitVector BV = it->second;
    if (statsA.OPSStatus.count(VD)) {
      statsA.OPSStatus[VD] |= BV;
    } else {
      statsA.OPSStatus[VD] = BV;
    }
  }
  for (auto it = statsB.OPSAllOwnedFields.begin(),
            ei = statsB.OPSAllOwnedFields.end();
       it != ei; ++it) {
    const VarDecl *VD = it->first;
    llvm::SmallSet<string, 10> value = statsB.OPSOwnedOwnedFields[VD];
    if (statsA.OPSAllOwnedFields.count(VD) &&
        !statsA.OPSOwnedOwnedFields.empty()) {
      if (!value.empty()) {
        for (auto s : value)
          statsA.OPSOwnedOwnedFields[VD].insert(s);
      }
    } else {
      statsA.OPSAllOwnedFields[VD] = value;
    }
  }

  for (auto it = statsB.SStatus.begin(), ei = statsB.SStatus.end(); it != ei;
       ++it) {
    const VarDecl *VD = it->first;
    const llvm::BitVector BV = it->second;
    if (statsA.SStatus.count(VD)) {
      statsA.SStatus[VD] |= BV;
    } else {
      statsA.SStatus[VD] = BV;
    }
  }
  for (auto it = statsB.SAllOwnedFields.begin(),
            ei = statsB.SAllOwnedFields.end();
       it != ei; ++it) {
    const VarDecl *VD = it->first;
    llvm::SmallSet<string, 10> OwnedValue = statsB.SOwnedOwnedFields[VD];
    llvm::SmallSet<string, 10> NullValue = statsB.SNullOwnedFields[VD];
    if (statsA.SAllOwnedFields.count(VD) &&
        (!statsA.SOwnedOwnedFields.empty() || !statsA.SNullOwnedFields.empty())) {
      if (!statsA.SOwnedOwnedFields.empty() && !OwnedValue.empty()) {
        for (auto s : OwnedValue)
          statsA.SOwnedOwnedFields[VD].insert(s);
      }
      if (!statsA.SNullOwnedFields.empty() && !NullValue.empty()) {
        for (auto s : NullValue)
          statsA.SNullOwnedFields[VD].insert(s);
      }
    } else {
      for (auto s : OwnedValue)
          statsA.SAllOwnedFields[VD].insert(s);
      for (auto s : NullValue)
          statsA.SAllOwnedFields[VD].insert(s);
    }
  }

  for (auto it = statsB.BOPStatus.begin(), ei = statsB.BOPStatus.end();
       it != ei; ++it) {
    const VarDecl *VD = it->first;
    const llvm::BitVector BV = it->second;
    if (statsA.BOPStatus.count(VD)) {
      statsA.BOPStatus[VD] |= BV;
    } else {
      statsA.BOPStatus[VD] = BV;
    }
  }
  for (auto it = statsB.BOPAllOwnedFields.begin(),
            ei = statsB.BOPAllOwnedFields.end();
       it != ei; ++it) {
    const VarDecl *VD = it->first;
    llvm::SmallSet<string, 10> value = statsB.BOPOwnedOwnedFields[VD];
    if (statsA.BOPAllOwnedFields.count(VD) &&
        !statsA.BOPOwnedOwnedFields.empty()) {
      if (!value.empty()) {
        for (auto s : value)
          statsA.BOPOwnedOwnedFields[VD].insert(s);
      }
    } else {
      statsA.BOPAllOwnedFields[VD] = value;
    }
  }

  return Ownership::OwnershipStatus(
      statsA.OPSStatus, statsA.OPSAllOwnedFields, statsA.OPSOwnedOwnedFields,
      statsA.SStatus, statsA.SAllOwnedFields, statsA.SOwnedOwnedFields,
      statsA.SNullOwnedFields,
      statsA.BOPStatus, statsA.BOPAllOwnedFields, statsA.BOPOwnedOwnedFields);
}

bool Ownership::OwnershipStatus::equals(const OwnershipStatus &V) const {
  return OPSStatus == V.OPSStatus && OPSAllOwnedFields == V.OPSAllOwnedFields &&
         OPSOwnedOwnedFields == V.OPSOwnedOwnedFields && SStatus == V.SStatus &&
         SAllOwnedFields == V.SAllOwnedFields &&
         SOwnedOwnedFields == V.SOwnedOwnedFields &&
         SNullOwnedFields == V.SNullOwnedFields && BOPStatus == V.BOPStatus &&
         BOPAllOwnedFields == V.BOPAllOwnedFields &&
         BOPOwnedOwnedFields == V.BOPOwnedOwnedFields;
}

bool Ownership::OwnershipStatus::is(const VarDecl *VD, Status S) const {
  if (OPSStatus.count(VD)) {
    auto it = OPSStatus.find(VD);
    llvm::BitVector status = it->second;
    unsigned bitIndex = getIndex(S);
    if (status.test(bitIndex)) {
      status.reset(bitIndex);
      return !status.any();
    }
    return false;
  }

  if (SStatus.count(VD)) {
    auto it = SStatus.find(VD);
    llvm::BitVector status = it->second;
    unsigned bitIndex = getIndex(S);
    if (status.test(bitIndex)) {
      status.reset(bitIndex);
      return !status.any();
    }
    return false;
  }

  if (BOPStatus.count(VD)) {
    auto it = BOPStatus.find(VD);
    llvm::BitVector status = it->second;
    unsigned bitIndex = getIndex(S);
    if (status.test(bitIndex)) {
      status.reset(bitIndex);
      return !status.any();
    }
    return false;
  }

  return false;
}

bool Ownership::OwnershipStatus::has(const VarDecl *VD, Status S) const {
  if (OPSStatus.count(VD)) {
    auto it = OPSStatus.find(VD);
    llvm::BitVector status = it->second;
    unsigned bitIndex = getIndex(S);
    if (status.test(bitIndex)) {
      status.reset(bitIndex);
      return status.any();
    }
    return false;
  }

  if (SStatus.count(VD)) {
    auto it = SStatus.find(VD);
    llvm::BitVector status = it->second;
    unsigned bitIndex = getIndex(S);
    if (status.test(bitIndex)) {
      status.reset(bitIndex);
      return status.any();
    }
    return false;
  }

  if (BOPStatus.count(VD)) {
    auto it = BOPStatus.find(VD);
    llvm::BitVector status = it->second;
    unsigned bitIndex = getIndex(S);
    if (status.test(bitIndex)) {
      status.reset(bitIndex);
      return status.any();
    }
    return false;
  }

  return false;
}

bool Ownership::OwnershipStatus::canAssign(const VarDecl *VD) const {
  unsigned uninitIndex = getIndex(Uninitialized);
  unsigned movedIndex = getIndex(Moved);
  unsigned nullIndex = getIndex(Null);
  if (OPSStatus.count(VD)) {
    auto it = OPSStatus.find(VD);
    llvm::BitVector status = it->second;

    if (status.test(uninitIndex)) {
      status.reset(uninitIndex);
    }
    if (status.test(movedIndex)) {
      status.reset(movedIndex);
    }
    if (status.test(nullIndex)) {
      status.reset(nullIndex);
    }
    return !status.any();
  }

  if (BOPStatus.count(VD)) {
    auto it = BOPStatus.find(VD);
    llvm::BitVector status = it->second;

    if (status.test(uninitIndex)) {
      status.reset(uninitIndex);
    }
    if (status.test(movedIndex)) {
      status.reset(movedIndex);
    }
    if (status.test(nullIndex)) {
      status.reset(nullIndex);
    }
    return !status.any();
  }

  return false;
}

void Ownership::OwnershipStatus::init(const VarDecl *VD) {
  QualType VDType = VD->getType();
  if (VDType->isPointerType()) {
    if (VDType->getPointeeType().getCanonicalType()->isRecordType()) {
      if (!OPSStatus.count(VD)) {
        if (const RecordType *RT = dyn_cast<RecordType>(
                VDType->getPointeeType().getCanonicalType())) {
          initOPS(RT->getDecl(), VD, Source::OPS);
        }
      }
    } else {
      if (!BOPStatus.count(VD)) {
        initBOP(VDType, VD, Source::BOP);
      }
    }
  } else {
    if (!SStatus.count(VD)) {
      if (const RecordType *RT =
              dyn_cast<RecordType>(VDType.getCanonicalType())) {
        initS(RT->getDecl(), VD, Source::S);
      }
    }
  }
}

void Ownership::OwnershipStatus::initOPS(const RecordDecl *RD,
                                         const VarDecl *VD, Source source,
                                         int depth, string parentFieldName) {
  if (depth == 0) {
    return;
  }
  // record all owned fields of VD in OPSAllOwnedFields
  for (RecordDecl::field_iterator it = RD->field_begin(), ei = RD->field_end();
       it != ei; ++it) {
    QualType FT = it->getType().getCanonicalType();
    string fieldName = parentFieldName + it->getNameAsString();
    if (IsTrackedType(FT)) {
      if (source == Source::OPS) {
        if (OPSAllOwnedFields[VD].empty()) {
          OPSAllOwnedFields[VD] = {};
          OPSOwnedOwnedFields[VD] = {};
        }
        if (!FT->isRecordType() || FT->isOwnedStructureType())
          OPSAllOwnedFields[VD].insert(fieldName);
      } else if (source == Source::S) {
        if (!FT->isRecordType() || FT->isOwnedStructureType())
          SAllOwnedFields[VD].insert(fieldName);
      } else {
        llvm_unreachable("Unexpected branch");
      }

      // if FT has owned fields,
      // recursively record all owned fields of FT in OPSAllOwnedFields[VD]
      if (FT->isPointerType() && FT.isOwnedQualified()) {
        if (const RecordType *RT =
                dyn_cast<RecordType>(FT->getPointeeType().getCanonicalType())) {
          if (RT->isOwnedStructureType()) {
            if (source == Source::OPS) {
              OPSAllOwnedFields[VD].insert(fieldName + "*");
            } else if (source == Source::S) {
              SAllOwnedFields[VD].insert(fieldName + "*");
            } else {
              llvm_unreachable("Unexpected branch");
            }
          }
          initOPS(RT->getDecl(), VD, source, depth - 1, fieldName + ".");
        } else {
          initBOP(FT, VD, source, depth - 1, fieldName);
        }
      }
      if (const RecordType *RT = dyn_cast<RecordType>(FT.getCanonicalType())) {
        if (RT->isOwnedStructureType()) {
          if (source == Source::OPS) {
            OPSAllOwnedFields[VD].insert(fieldName);
          } else if (source == Source::S) {
            SAllOwnedFields[VD].insert(fieldName);
          } else {
            llvm_unreachable("Unexpected branch");
          }
        }
        initS(RT->getDecl(), VD, source, depth - 1, fieldName + ".");
      }
    }
  }
  // set VD to UNINITIALIZED
  if (source == Source::OPS && depth == 10) {
    OPSStatus[VD] = llvm::BitVector(7, 0);
    set(VD, Ownership::Status::Uninitialized);
  }
}

void Ownership::OwnershipStatus::initS(const RecordDecl *RD, const VarDecl *VD,
                                       Source source, int depth,
                                       string parentFieldName) {
  if (depth == 0) {
    return;
  }

  // owned struct special manipulation
  if (VD->getType().getTypePtr()->isOwnedStructureType()) {
    if (source == Source::S) {
      if (SAllOwnedFields[VD].empty()) {
        SAllOwnedFields[VD] = {};
        SOwnedOwnedFields[VD] = {};
        SNullOwnedFields[VD] = {};
      }
    }
  }

  // record all owned fields ofr VD in SAllOwnedFields
  for (RecordDecl::field_iterator it = RD->field_begin(), ei = RD->field_end();
       it != ei; ++it) {
    QualType FT = it->getType().getCanonicalType();
    string fieldName = parentFieldName + it->getNameAsString();
    if (IsTrackedType(FT)) {
      if (source == Source::OPS) {
        if (!FT->isRecordType() || FT->isOwnedStructureType())
          OPSAllOwnedFields[VD].insert(fieldName);
      } else if (source == Source::S) {
        if (SAllOwnedFields[VD].empty()) {
          SAllOwnedFields[VD] = {};
          SOwnedOwnedFields[VD] = {};
          SNullOwnedFields[VD] = {};
        }
        if (!FT->isRecordType() || FT->isOwnedStructureType())
          SAllOwnedFields[VD].insert(fieldName);
      } else {
        llvm_unreachable("Unexpected branch");
      }

      // recursively record all owned fields
      if (FT->isPointerType() && FT.isOwnedQualified()) {
        if (const RecordType *RT =
                dyn_cast<RecordType>(FT->getPointeeType().getCanonicalType())) {
          if (RT->isOwnedStructureType()) {
            if (source == Source::OPS) {
              OPSAllOwnedFields[VD].insert(fieldName + "*");
            } else if (source == Source::S) {
              SAllOwnedFields[VD].insert(fieldName + "*");
            } else {
              llvm_unreachable("Unexpected branch");
            }
          }
          initOPS(RT->getDecl(), VD, source, depth - 1, fieldName + ".");
        } else {
          initBOP(FT, VD, source, depth - 1, fieldName);
        }
      }
      if (const RecordType *RT = dyn_cast<RecordType>(FT.getCanonicalType())) {
        if (RT->isOwnedStructureType()) {
          if (source == Source::OPS) {
            OPSAllOwnedFields[VD].insert(fieldName);
          } else if (source == Source::S) {
            SAllOwnedFields[VD].insert(fieldName);
          } else {
            llvm_unreachable("Unexpected branch");
          }
        }
        initS(RT->getDecl(), VD, source, depth - 1, fieldName + ".");
      }
    }
  }
  // set VD to UNINITIALIZED
  if (source == Source::S && depth == 10) {
    SStatus[VD] = llvm::BitVector(7, 0);
    set(VD, Ownership::Status::Uninitialized);
  }
}

void Ownership::OwnershipStatus::initBOP(QualType QT, const VarDecl *VD,
                                         Source source, int depth,
                                         string parentFieldName) {
  if (depth == 0) {
    return;
  }
  string fieldName;
  QT = QT->getPointeeType().getCanonicalType();
  while (true) {
    fieldName += "*";
    if (QT->isPointerType() && QT.isOwnedQualified()) {
      if (source == Source::OPS) {
        OPSAllOwnedFields[VD].insert(parentFieldName + fieldName);
      } else if (source == Source::S) {
        SAllOwnedFields[VD].insert(parentFieldName + fieldName);
      } else {
        if (BOPAllOwnedFields[VD].empty()) {
          BOPAllOwnedFields[VD] = {};
          BOPOwnedOwnedFields[VD] = {};
        }
        BOPAllOwnedFields[VD].insert(fieldName);
      }
      QT = QT->getPointeeType().getCanonicalType();
    } else {
      break;
    }
  }
  // set VD to UNINITIALIZED
  if (source == Source::BOP) {
    BOPStatus[VD] = llvm::BitVector(7, 0);
    set(VD, Ownership::Status::Uninitialized);
  }
}

void Ownership::OwnershipStatus::set(const VarDecl *VD, Status S) {
  if (OPSStatus.count(VD)) {
    llvm::BitVector &status = OPSStatus[VD];
    unsigned bitIndex = getIndex(S);
    status.set(bitIndex);
  }

  if (SStatus.count(VD)) {
    llvm::BitVector &status = SStatus[VD];
    unsigned bitIndex = getIndex(S);
    status.set(bitIndex);
  }

  if (BOPStatus.count(VD)) {
    llvm::BitVector &status = BOPStatus[VD];
    unsigned bitIndex = getIndex(S);
    status.set(bitIndex);
  }
}

void Ownership::OwnershipStatus::reset(const VarDecl *VD, Status S) {
  if (OPSStatus.count(VD)) {
    llvm::BitVector &status = OPSStatus[VD];
    unsigned bitIndex = getIndex(S);
    status.reset(bitIndex);
  }

  if (SStatus.count(VD)) {
    llvm::BitVector &status = SStatus[VD];
    unsigned bitIndex = getIndex(S);
    status.reset(bitIndex);
  }

  if (BOPStatus.count(VD)) {
    llvm::BitVector &status = BOPStatus[VD];
    unsigned bitIndex = getIndex(S);
    status.reset(bitIndex);
  }
}

void Ownership::OwnershipStatus::resetAll(const VarDecl *VD) {
  if (OPSStatus.count(VD)) {
    llvm::BitVector &status = OPSStatus[VD];
    for (unsigned index = 0; index < 7; index++)
      status.reset(index);
  }

  if (SStatus.count(VD)) {
    llvm::BitVector &status = SStatus[VD];
    for (unsigned index = 0; index < 7; index++)
      status.reset(index);
  }

  if (BOPStatus.count(VD)) {
    llvm::BitVector &status = BOPStatus[VD];
    for (unsigned index = 0; index < 7; index++)
      status.reset(index);
  }
}

void Ownership::OwnershipStatus::setToOwned(const VarDecl *VD) {
  if (OPSStatus.count(VD)) {
    resetAll(VD);
    set(VD, Ownership::Status::Owned);
    OPSOwnedOwnedFields[VD] = OPSAllOwnedFields[VD];
  }

  if (SStatus.count(VD)) {
    resetAll(VD);
    set(VD, Ownership::Status::Owned);
    SOwnedOwnedFields[VD] = SAllOwnedFields[VD];
  }

  if (BOPStatus.count(VD)) {
    resetAll(VD);
    set(VD, Ownership::Status::Owned);
    BOPOwnedOwnedFields[VD] = BOPAllOwnedFields[VD];
  }
}

void Ownership::OwnershipStatus::setToNull(const VarDecl *VD) {
  if (OPSStatus.count(VD)) {
    OPSOwnedOwnedFields[VD].clear();
    resetAll(VD);
    set(VD, Ownership::Status::Null);
  }
  if (BOPStatus.count(VD)) {
    BOPOwnedOwnedFields[VD].clear();
    resetAll(VD);
    set(VD, Ownership::Status::Null);
  }
}

void Ownership::OwnershipStatus::setToNull(const Expr *E) {
  if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(E)) {
    const VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl());
    setToNull(VD);
    return;
  }
  if (const MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
    pair<const Expr *, string> memberField = getMemberFullField(ME);
    if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(memberField.first)) {
      const VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl());
      if (OPSStatus.count(VD)) {
        if (OPSAllOwnedFields[VD].count(memberField.second)) {
          OPSOwnedOwnedFields[VD].erase(memberField.second);
          auto allPrefixStrs = findPrefixStrings(OPSAllOwnedFields[VD],
                                                 memberField.second + ".");
          for (const string &str : allPrefixStrs) {
            OPSOwnedOwnedFields[VD].erase(str);
          }
        }
      }
      if (SStatus.count(VD)) {
        if (SAllOwnedFields[VD].count(memberField.second)) {
          SOwnedOwnedFields[VD].erase(memberField.second);
          SNullOwnedFields[VD].insert(memberField.second);
          auto allPrefixStrs =
              findPrefixStrings(SAllOwnedFields[VD], memberField.second + ".");
          for (const string &str : allPrefixStrs) {
            SOwnedOwnedFields[VD].erase(str);
            SNullOwnedFields[VD].insert(str);
          }
        }
      }
    }
  }
  if (const UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
    string suffix;
    const Expr *e = UO;
    while (UO->getOpcode() == UO_Deref) {
      if (const ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(e)) {
        e = ICE->getSubExpr();
      } else if (const UnaryOperator *uo = dyn_cast<UnaryOperator>(e)) {
        UO = uo;
        suffix += "*";
        e = UO->getSubExpr();
      } else {
        break;
      }
    }
    if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(e)) {
      const VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl());
      if (BOPStatus.count(VD)) {
        if (BOPAllOwnedFields[VD].count(suffix)) {
          BOPOwnedOwnedFields[VD].erase(suffix);
          auto allPrefixStrs =
              findPrefixStrings(BOPAllOwnedFields[VD], suffix + "*");
          for (const string &str : allPrefixStrs) {
            BOPOwnedOwnedFields[VD].erase(str);
          }
          if (BOPAllOwnedFields[VD].size() != BOPOwnedOwnedFields[VD].size()) {
            if (!is(VD, Moved)) {
              resetAll(VD);
              set(VD, PartialMoved);
            }
          }
          if (BOPOwnedOwnedFields[VD].empty()) {
            if (!is(VD, Moved)) {
              resetAll(VD);
              set(VD, AllMoved);
            }
          }
        }
      }
    }
  }
}

string Ownership::OwnershipStatus::collectMovedFields(const VarDecl *VD) {
  llvm::SmallSet<string, 10> allFields, ownedFields;
  if (OPSStatus.count(VD)) {
    allFields = OPSAllOwnedFields[VD];
    ownedFields = OPSOwnedOwnedFields[VD];
  } else if (SStatus.count(VD)) {
    allFields = SAllOwnedFields[VD];
    ownedFields = SOwnedOwnedFields[VD];
  } else if (BOPStatus.count(VD)) {
    allFields = BOPAllOwnedFields[VD];
    ownedFields = BOPOwnedOwnedFields[VD];
  }
  string movedFields = "";
  int count = 0;
  for (const auto &element : allFields) {
    if (ownedFields.count(element) == 0) {
      if (count++ != 0) {
        movedFields += ", ";
      }
      if (VD->getType()->isPointerType() &&
          !VD->getType()->getPointeeType().getCanonicalType()->isRecordType()) {
        movedFields = movedFields + element + VD->getNameAsString();
      } else {
        movedFields = movedFields + moveAsterisksToFront(VD->getNameAsString() +
                                                         "." + element);
      }
    }
  }
  if (count > 1) {
    movedFields += " are";
  } else {
    movedFields += " is";
  }
  return movedFields;
}

SmallVector<OwnershipDiagInfo, 3> Ownership::OwnershipStatus::checkOPSUse(
    const VarDecl *VD, const SourceLocation &Loc, bool isGetAddr, bool isStar) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // when use ops, we must ensure the variable is owned

  // check the status of the variable
  if (!is(VD, Ownership::Status::Owned)) {
    if (has(VD, Ownership::Status::Moved) || is(VD, Ownership::Status::Moved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidUseOfMoved, VD->getNameAsString()));
    } else if (is(VD, Ownership::Status::Uninitialized)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidUseOfUninit, VD->getNameAsString()));
    } else if (has(VD, Ownership::Status::Uninitialized)) {
      diags.push_back(
          OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfPossiblyUninit,
                            VD->getNameAsString()));
    } else if (is(VD, Ownership::Status::PartialMoved)) {
      diags.push_back(
          OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfPartiallyMoved,
                            VD->getNameAsString(), collectMovedFields(VD)));
    } else if (is(VD, Ownership::Status::AllMoved)) {
      diags.push_back(
          OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfAllMoved,
                            VD->getNameAsString(), collectMovedFields(VD)));
    }
  }
  if (!isGetAddr) {
    // change the status to moved
    OPSOwnedOwnedFields[VD].clear();
    resetAll(VD);
    if (!isStar) {
      set(VD, Ownership::Status::Moved);
    } else {
      set(VD, AllMoved);
    }
  }
  return diags;
}

SmallVector<OwnershipDiagInfo, 3> Ownership::OwnershipStatus::checkOPSFieldUse(
    const VarDecl *VD, const SourceLocation &Loc, string fullFieldName,
    bool isGetAddr) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // when assign a field, we check three conditions:
  // 1. the field's parent must be owned
  // 2. the status of VD must not be moved or uninit
  // 3. the field and the field's subfields must be all moved

  // check condition 1
  int index = fullFieldName.length() - 2;
  string current = fullFieldName;
  while (index > 0) {
    if (current[index] == '*') {
      current = current.substr(0, index + 1);
      index--;
    } else {
      size_t pos = current.find_last_of('.');
      if (pos != string::npos) {
        current = current.substr(0, pos);
        index = pos;
      } else {
        break;
      }
    }
    if (OPSAllOwnedFields[VD].count(current) &&
        !OPSOwnedOwnedFields[VD].count(current)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidUseOfMoved,
          moveAsterisksToFront(VD->getNameAsString() + "." + current)));
      break;
    }
  }

  // check condition 2
  if ((is(VD, Moved) || has(VD, Moved)) && diags.empty()) {
    diags.push_back(
        OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfMoved,
                          VD->getNameAsString() + "." + fullFieldName));
  }
  if ((is(VD, Uninitialized) || has(VD, Uninitialized)) && diags.empty()) {
    diags.push_back(
        OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfUninit,
                          VD->getNameAsString() + "." + fullFieldName));
  }

  // check condition 3
  // if fullFieldName has been moved, report error
  if (OPSAllOwnedFields[VD].count(fullFieldName) && !OPSOwnedOwnedFields[VD].count(fullFieldName)) {
    diags.push_back(
        OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfMoved,
                          VD->getNameAsString() + "." + fullFieldName));
  }
  // calculate the fields with fullFieldName prefix
  llvm::SmallSet<string, 10> allPrefixStrs;
  if (fullFieldName[fullFieldName.size() - 1] == '.') {
     allPrefixStrs = findPrefixStrings(OPSAllOwnedFields[VD], fullFieldName);
  } else {
    allPrefixStrs = findPrefixStrings(OPSAllOwnedFields[VD], fullFieldName + ".");
  }
  auto allPrefixStrsStar =
      findPrefixStrings(OPSAllOwnedFields[VD], fullFieldName + "*");
  for (auto elem : allPrefixStrsStar) {
    allPrefixStrs.insert(elem);
  }
  llvm::SmallSet<string, 10> ownedPrefixStrs;
  if (fullFieldName[fullFieldName.size() - 1] == '.') {
    ownedPrefixStrs = findPrefixStrings(OPSOwnedOwnedFields[VD], fullFieldName);
  } else {
    ownedPrefixStrs = findPrefixStrings(OPSOwnedOwnedFields[VD], fullFieldName + ".");
  }
  auto ownedPrefixStrsStar =
      findPrefixStrings(OPSOwnedOwnedFields[VD], fullFieldName + "*");
  for (auto elem : ownedPrefixStrsStar) {
    ownedPrefixStrs.insert(elem);
  }
  if (allPrefixStrs.size() != ownedPrefixStrs.size() && diags.empty()) {
    diags.push_back(
        OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfPartiallyMoved,
                          VD->getNameAsString(), collectMovedFields(VD)));
  }
  if (!isGetAddr) {
    // change the status of the fields
    OPSOwnedOwnedFields[VD].erase(fullFieldName);
    // remove ownedPrefixStrs from OPSOwnedOwnedFields
    for (auto str : ownedPrefixStrs) {
      OPSOwnedOwnedFields[VD].erase(str);
    }
    if (OPSAllOwnedFields[VD].size() != OPSOwnedOwnedFields[VD].size()) {
      if (!is(VD, Ownership::Status::Moved)) {
        resetAll(VD);
        set(VD, Ownership::Status::PartialMoved);
      }
    }
    if (!OPSAllOwnedFields[VD].empty() && OPSOwnedOwnedFields[VD].empty() &&
        !VD->getType()->getPointeeType()->isOwnedStructureType()) {
      if (!is(VD, Ownership::Status::Moved)) {
        resetAll(VD);
        set(VD, Ownership::Status::AllMoved);
      }
    }
  }

  return diags;
}

SmallVector<OwnershipDiagInfo, 3>
Ownership::OwnershipStatus::checkOPSAssign(const VarDecl *VD,
                                           const SourceLocation &Loc) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // when assign ops, we must ensure the variable is uninit or moved

  // check the status of the variable
  if (!canAssign(VD)) {
    if (has(VD, Ownership::Status::Owned) || is(VD, Ownership::Status::Owned)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfOwned, VD->getNameAsString()));
    } else if (is(VD, Ownership::Status::PartialMoved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfPartiallyMoved,
          VD->getNameAsString(), collectMovedFields(VD)));
    } else if (has(VD, Ownership::Status::PartialMoved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfPossiblyPartiallyMoved,
          VD->getNameAsString(), collectMovedFields(VD)));
    } else if (is(VD, AllMoved)) {
      diags.push_back(
          OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidAssignOfAllMoved,
                            VD->getNameAsString()));
    }
  }
  // change the status to owned
  OPSOwnedOwnedFields[VD] = OPSAllOwnedFields[VD];
  resetAll(VD);
  set(VD, Ownership::Status::Owned);

  return diags;
}

SmallVector<OwnershipDiagInfo, 3>
Ownership::OwnershipStatus::checkOPSAssignStar(const VarDecl *VD,
                                               const SourceLocation &Loc) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  if (!is(VD, AllMoved)) {
    if (has(VD, Ownership::Status::Owned) || is(VD, Ownership::Status::Owned)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfOwned, VD->getNameAsString()));
    } else if (is(VD, Ownership::Status::PartialMoved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfPartiallyMoved,
          VD->getNameAsString(), collectMovedFields(VD)));
    } else if (has(VD, Ownership::Status::PartialMoved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfPossiblyPartiallyMoved,
          VD->getNameAsString(), collectMovedFields(VD)));
    }
  }

  if (diags.empty()) {
    OPSOwnedOwnedFields[VD] = OPSAllOwnedFields[VD];
    resetAll(VD);
    set(VD, Owned);
  }
  return diags;
}

SmallVector<OwnershipDiagInfo, 3>
Ownership::OwnershipStatus::checkOPSFieldAssign(const VarDecl *VD,
                                                const SourceLocation &Loc,
                                                string fullFieldName) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // when assign a field, we check three conditions:
  // 1. the field's parent must be owned
  // 2. the status of VD must not be moved or uninit
  // 3. the field and the field's subfields must be all moved

  // check condition 1
  int index = fullFieldName.length() - 2;
  string current = fullFieldName;
  while (index > 0) {
    if (current[index] == '*') {
      current = current.substr(0, index + 1);
      index--;
    } else {
      size_t pos = current.find_last_of('.');
      if (pos != string::npos) {
        current = current.substr(0, pos);
        index = pos;
      } else {
        break;
      }
    }
    if (OPSAllOwnedFields[VD].count(current) &&
        !OPSOwnedOwnedFields[VD].count(current)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignFieldOfMoved,
          moveAsterisksToFront(VD->getNameAsString() + "." + current)));
      return diags;
    }
  }

  // check condition 2
  if ((is(VD, Moved) || has(VD, Moved)) && diags.empty()) {
    diags.push_back(
        OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidAssignFieldOfMoved,
                          VD->getNameAsString()));
  }
  if ((is(VD, Uninitialized) || has(VD, Uninitialized)) && diags.empty()) {
    diags.push_back(
        OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidAssignFieldOfUninit,
                          VD->getNameAsString()));
  }

  // check condition 3
  if (OPSAllOwnedFields[VD].count(fullFieldName) && OPSOwnedOwnedFields[VD].count(fullFieldName) && diags.empty()) {
    diags.push_back(
        OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidAssignFieldOfOwned,
                          VD->getNameAsString() + "." + fullFieldName));
  }
  // calculate the fields with fullFieldName prefix
  llvm::SmallSet<string, 10> allPrefixStrs;
  if (fullFieldName[fullFieldName.size() - 1] == '.') {
     allPrefixStrs = findPrefixStrings(OPSAllOwnedFields[VD], fullFieldName);
  } else {
    allPrefixStrs = findPrefixStrings(OPSAllOwnedFields[VD], fullFieldName + ".");
  }
  auto allPrefixStrsStar =
      findPrefixStrings(OPSAllOwnedFields[VD], fullFieldName + "*");
  for (auto elem : allPrefixStrsStar) {
    allPrefixStrs.insert(elem);
  }
  llvm::SmallSet<string, 10> ownedPrefixStrs;
  if (fullFieldName[fullFieldName.size() - 1] == '.') {
    ownedPrefixStrs = findPrefixStrings(OPSOwnedOwnedFields[VD], fullFieldName);
  } else {
    ownedPrefixStrs = findPrefixStrings(OPSOwnedOwnedFields[VD], fullFieldName + ".");
  }
  auto ownedPrefixStrsStar =
      findPrefixStrings(OPSOwnedOwnedFields[VD], fullFieldName + "*");
  for (auto elem : ownedPrefixStrsStar) {
    ownedPrefixStrs.insert(elem);
  }
  if (!ownedPrefixStrs.empty() && diags.empty()) {
    diags.push_back(OwnershipDiagInfo(
        Loc, OwnershipDiagKind::InvalidAssignSubFieldOwned,
        VD->getNameAsString(), concatFields(VD, ownedPrefixStrs)));
  }
  if (!is(VD, Ownership::Status::Moved)) {
    if (OPSAllOwnedFields[VD].count(fullFieldName)) {
      OPSOwnedOwnedFields[VD].insert(fullFieldName);
    }
    // add allPrefixStrs to OPSOwnedOwnedFields
    for (auto str : allPrefixStrs) {
      OPSOwnedOwnedFields[VD].insert(str);
    }
  }
  if (OPSAllOwnedFields[VD].size() == OPSOwnedOwnedFields[VD].size()) {
    if (!is(VD, Ownership::Status::Owned) &&
        !is(VD, Ownership::Status::Moved)) {
      resetAll(VD);
      set(VD, Ownership::Status::Owned);
    }
  }
  if (OPSAllOwnedFields[VD].size() != OPSOwnedOwnedFields[VD].size()) {
    if (!is(VD, Ownership::Status::Owned) &&
        !is(VD, Ownership::Status::Moved)) {
      resetAll(VD);
      set(VD, Ownership::Status::PartialMoved);
    }
  }

  return diags;
}

SmallVector<OwnershipDiagInfo, 3> Ownership::OwnershipStatus::checkSUse(
    const VarDecl *VD, const SourceLocation &Loc, bool isGetAddr) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // owned struct special manipulation
  if (VD->getType().getTypePtr()->isOwnedStructureType()) {
    if (!is(VD, Owned)) {
      if (is(VD, Uninitialized) || has(VD, Uninitialized)) {
        diags.push_back(OwnershipDiagInfo(
            Loc, OwnershipDiagKind::InvalidUseOfUninit, VD->getNameAsString()));
      } else if (is(VD, Moved) || has(VD, Moved)) {
        diags.push_back(OwnershipDiagInfo(
            Loc, OwnershipDiagKind::InvalidUseOfMoved, VD->getNameAsString()));
      }
    }
    if (!isGetAddr) {
      resetAll(VD);
      set(VD, Moved);
    }
  }

  if (SAllOwnedFields[VD].size() - SOwnedOwnedFields[VD].size() - SNullOwnedFields[VD].size() != 0 &&
      SAllOwnedFields[VD].size()!= SOwnedOwnedFields[VD].size() &&
      diags.empty()) {
    diags.push_back(OwnershipDiagInfo(Loc, InvalidUseOfPartiallyMoved,
                                      VD->getNameAsString(),
                                      collectMovedFields(VD)));
  }
  if (!isGetAddr)
    SOwnedOwnedFields[VD].clear();
  return diags;
}

SmallVector<OwnershipDiagInfo, 3> Ownership::OwnershipStatus::checkSFieldUse(
    const VarDecl *VD, const SourceLocation &Loc, string fullFieldName,
    bool isGetAddr) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // owned struct special manipulation
  if (VD->getType().getTypePtr()->isOwnedStructureType()) {
    if (is(VD, Uninitialized)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidUseOfUninit, VD->getNameAsString()));
    } else if (is(VD, Moved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidUseOfMoved, VD->getNameAsString()));
    }
  }

  if (SAllOwnedFields[VD].count(fullFieldName) && !SOwnedOwnedFields[VD].count(fullFieldName) && diags.empty()) {
    diags.push_back(
        OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfMoved,
                          VD->getNameAsString() + "." + fullFieldName));
  }
  // calculate the fields with fullFieldName prefix
  llvm::SmallSet<string, 10> allPrefixStrs;
  if (fullFieldName[fullFieldName.size() - 1] == '.') {
     allPrefixStrs = findPrefixStrings(SAllOwnedFields[VD], fullFieldName);
  } else {
    allPrefixStrs = findPrefixStrings(SAllOwnedFields[VD], fullFieldName + ".");
  }
  auto allPrefixStrsStar =
      findPrefixStrings(SAllOwnedFields[VD], fullFieldName + "*");
  for (auto elem : allPrefixStrsStar) {
    allPrefixStrs.insert(elem);
  }
  llvm::SmallSet<string, 10> ownedPrefixStrs;
  if (fullFieldName[fullFieldName.size() - 1] == '.') {
    ownedPrefixStrs = findPrefixStrings(SOwnedOwnedFields[VD], fullFieldName);
  } else {
    ownedPrefixStrs = findPrefixStrings(SOwnedOwnedFields[VD], fullFieldName + ".");
  }
  auto ownedPrefixStrsStar =
      findPrefixStrings(SOwnedOwnedFields[VD], fullFieldName + "*");
  for (auto elem : ownedPrefixStrsStar) {
    ownedPrefixStrs.insert(elem);
  }
  if (allPrefixStrs.size() != ownedPrefixStrs.size() && diags.empty()) {
    diags.push_back(OwnershipDiagInfo(
        Loc, OwnershipDiagKind::InvalidUseOfPartiallyMoved,
        VD->getNameAsString() + "." + fullFieldName, collectMovedFields(VD)));
  }
  if (!isGetAddr) {
    SOwnedOwnedFields[VD].erase(fullFieldName);
    for (auto str : ownedPrefixStrs) {
      SOwnedOwnedFields[VD].erase(str);
    }
  }

  return diags;
}

SmallVector<OwnershipDiagInfo, 3>
Ownership::OwnershipStatus::checkSAssign(const VarDecl *VD,
                                         const SourceLocation &Loc) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // special handling is required for owned struct: do not check ownership when reassign, for example:
  // @code
  // owned struct S s1 = init();
  // owned struct S s2 = init();
  // s2 = s1; // Ok
  // @endcode
  if (VD->getType().getTypePtr()->isOwnedStructureType()) {
    resetAll(VD);
    set(VD, Owned);
  }

  // when assign a struct, all of its owned fields must be MOVED
  if (!SOwnedOwnedFields[VD].empty() && diags.empty()) {
    if (SAllOwnedFields[VD].size() == SOwnedOwnedFields[VD].size()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfOwned, VD->getNameAsString()));
    } else {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfPartiallyMoved,
          VD->getNameAsString(), collectMovedFields(VD)));
    }
  }
  SOwnedOwnedFields[VD] = SAllOwnedFields[VD];

  return diags;
}

SmallVector<OwnershipDiagInfo, 3> Ownership::OwnershipStatus::checkSFieldAssign(
    const VarDecl *VD, const SourceLocation &Loc, string fullFieldName) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // owned struct special manipulation
  if (VD->getType().getTypePtr()->isOwnedStructureType()) {
    if (!is(VD, Owned)) {
      if (is(VD, Uninitialized) || has(VD, Uninitialized)) {
        diags.push_back(OwnershipDiagInfo(
            Loc, OwnershipDiagKind::InvalidAssignFieldOfUninit,
            VD->getNameAsString()));
      } else if (is(VD, Moved) || has(VD, Moved)) {
        diags.push_back(
            OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidAssignFieldOfMoved,
                              VD->getNameAsString()));
      }
    }
  }

  // when assign a field, we check two conditions:
  // 1. the field's parent must be owned
  // 2. the field and the field's subfields must be all moved

  // check condition 1
  int index = fullFieldName.length() - 2;
  string current = fullFieldName;
  while (index > 0) {
    if (current[index] == '*') {
      current = current.substr(0, index + 1);
      index--;
    } else {
      size_t pos = current.find_last_of('.');
      if (pos != string::npos) {
        current = current.substr(0, pos);
        index = pos;
      } else {
        break;
      }
    }
    if (SAllOwnedFields[VD].count(current) &&
        !SOwnedOwnedFields[VD].count(current) && diags.empty()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignFieldOfMoved,
          moveAsterisksToFront(VD->getNameAsString() + "." + current)));
      return diags;
    }
  }

  // check condition 2
  if (SAllOwnedFields[VD].count(fullFieldName) && SOwnedOwnedFields[VD].count(fullFieldName) && diags.empty()) {
    diags.push_back(OwnershipDiagInfo(
        Loc, OwnershipDiagKind::InvalidAssignFieldOfOwned,
        moveAsterisksToFront(VD->getNameAsString() + "." + fullFieldName)));
  }
  // calculate the fields with fullFieldName prefix
  llvm::SmallSet<string, 10> allPrefixStrs;
  if (fullFieldName[fullFieldName.size() - 1] == '.') {
     allPrefixStrs = findPrefixStrings(SAllOwnedFields[VD], fullFieldName);
  } else {
    allPrefixStrs = findPrefixStrings(SAllOwnedFields[VD], fullFieldName + ".");
  }
  auto allPrefixStrsStar =
      findPrefixStrings(SAllOwnedFields[VD], fullFieldName + "*");
  for (auto elem : allPrefixStrsStar) {
    allPrefixStrs.insert(elem);
  }
  llvm::SmallSet<string, 10> ownedPrefixStrs;
  if (fullFieldName[fullFieldName.size() - 1] == '.') {
    ownedPrefixStrs = findPrefixStrings(SOwnedOwnedFields[VD], fullFieldName);
  } else {
    ownedPrefixStrs = findPrefixStrings(SOwnedOwnedFields[VD], fullFieldName + ".");
  }
  auto ownedPrefixStrsStar =
      findPrefixStrings(SOwnedOwnedFields[VD], fullFieldName + "*");
  for (auto elem : ownedPrefixStrsStar) {
    ownedPrefixStrs.insert(elem);
  }
  if (!ownedPrefixStrs.empty() && diags.empty()) {
    diags.push_back(OwnershipDiagInfo(
        Loc, OwnershipDiagKind::InvalidAssignSubFieldOwned,
        VD->getNameAsString(), concatFields(VD, ownedPrefixStrs)));
  }
  // change the status of the fields
  if (SAllOwnedFields[VD].count(fullFieldName))
    SOwnedOwnedFields[VD].insert(fullFieldName);
  // add allPrefixStrs to SOwnedOwnedFields
  for (auto str : allPrefixStrs) {
    SOwnedOwnedFields[VD].insert(str);
  }

  return diags;
}

SmallVector<OwnershipDiagInfo, 3> Ownership::OwnershipStatus::checkBOPUse(
    const VarDecl *VD, const SourceLocation &Loc, bool isGetAddr) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // check the status of the variable
  if (!is(VD, Ownership::Status::Owned)) {
    if (has(VD, Ownership::Status::Moved) || is(VD, Ownership::Status::Moved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidUseOfMoved, VD->getNameAsString()));
    } else if (is(VD, Ownership::Status::Uninitialized)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidUseOfUninit, VD->getNameAsString()));
    } else if (has(VD, Ownership::Status::Uninitialized)) {
      diags.push_back(
          OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfPossiblyUninit,
                            VD->getNameAsString()));
    } else if (is(VD, Ownership::Status::PartialMoved)) {
      diags.push_back(
          OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfPartiallyMoved,
                            VD->getNameAsString(), collectMovedFields(VD)));
    } else if (is(VD, AllMoved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidUseOfAllMoved, VD->getNameAsString()));
    }
  }
  if (!isGetAddr) {
    // change the status to moved
    if (!is(VD, Uninitialized)) {
      BOPOwnedOwnedFields[VD].clear();
      resetAll(VD);
      set(VD, Ownership::Status::Moved);
    }
  }

  return diags;
}

SmallVector<OwnershipDiagInfo, 3> Ownership::OwnershipStatus::checkBOPFieldUse(
    const VarDecl *VD, const SourceLocation &Loc, string fullFieldName,
    bool isGetAddr) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // check field's parent
  for (int i = fullFieldName.length() - 2; i > 0; i--) {
    string current = fullFieldName.substr(0, i + 1);
    if (BOPAllOwnedFields[VD].count(current) &&
        !BOPOwnedOwnedFields[VD].count(current)) {
      diags.push_back(OwnershipDiagInfo(Loc,
                                        OwnershipDiagKind::InvalidUseOfMoved,
                                        fullFieldName + VD->getNameAsString()));
      break;
    }
  }
  if ((is(VD, Ownership::Status::Moved) || has(VD, Ownership::Status::Moved)) &&
      diags.empty()) {
    diags.push_back(OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfMoved,
                                      VD->getNameAsString()));
  }

  // if the field is owned qualified, check the field and its child
  if (BOPAllOwnedFields[VD].count(fullFieldName)) {
    // if fullFieldName has been moved, report error
    if (!BOPOwnedOwnedFields[VD].count(fullFieldName) && diags.empty()) {
      diags.push_back(OwnershipDiagInfo(Loc,
                                        OwnershipDiagKind::InvalidUseOfMoved,
                                        fullFieldName + VD->getNameAsString()));
    }
    // calculate the fields with fullFieldName prefix
    auto allPrefixStrs =
        findPrefixStrings(BOPAllOwnedFields[VD], fullFieldName);
    auto ownedPrefixStrs =
        findPrefixStrings(BOPOwnedOwnedFields[VD], fullFieldName);
    if (allPrefixStrs.size() != ownedPrefixStrs.size() && diags.empty()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidUseOfPartiallyMoved,
          fullFieldName + VD->getNameAsString(), collectMovedFields(VD)));
    }
    if (!isGetAddr) {
      // change the status of the fields
      BOPOwnedOwnedFields[VD].erase(fullFieldName);
      // remove ownedPrefixStrs from BOPOwnedOwnedFields
      for (auto str : ownedPrefixStrs) {
        BOPOwnedOwnedFields[VD].erase(str);
      }
      if (BOPAllOwnedFields[VD].size() != BOPOwnedOwnedFields[VD].size()) {
        if (!is(VD, Ownership::Status::Moved)) {
          resetAll(VD);
          set(VD, Ownership::Status::PartialMoved);
        }
      }
      if (BOPOwnedOwnedFields[VD].empty()) {
        if (!is(VD, Ownership::Status::Moved)) {
          resetAll(VD);
          set(VD, Ownership::Status::AllMoved);
        }
      }
    }
  }

  return diags;
}

SmallVector<OwnershipDiagInfo, 3>
Ownership::OwnershipStatus::checkBOPAssign(const VarDecl *VD,
                                           const SourceLocation &Loc) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // check the status of the variable
  if (!canAssign(VD)) {
    if (has(VD, Ownership::Status::Owned) || is(VD, Ownership::Status::Owned)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfOwned, VD->getNameAsString()));
    } else if (is(VD, Ownership::Status::PartialMoved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfPartiallyMoved,
          VD->getNameAsString(), collectMovedFields(VD)));
    } else if (has(VD, Ownership::Status::PartialMoved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignOfPossiblyPartiallyMoved,
          VD->getNameAsString(), collectMovedFields(VD)));
    } else if (is(VD, AllMoved)) {
      diags.push_back(
          OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidAssignOfAllMoved,
                            VD->getNameAsString()));
    }
  }
  // change the status to owned
  BOPOwnedOwnedFields[VD] = BOPAllOwnedFields[VD];
  resetAll(VD);
  set(VD, Ownership::Status::Owned);

  return diags;
}

SmallVector<OwnershipDiagInfo, 3>
Ownership::OwnershipStatus::checkBOPFieldAssign(const VarDecl *VD,
                                                const SourceLocation &Loc,
                                                string fullFieldName) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  // for a non owned qualified field, just check its parent
  // for a owned qualified field, we check three conditions:
  // // 1. the status of VD must be PartiallyMoved or AllMoved
  // // 2. the field's parents must be not moved
  // // 3. the field and the field's subfields must be all moved

  // the parent field must be owned
  for (int i = fullFieldName.length() - 2; i > 0; i--) {
    string current = fullFieldName.substr(0, i + 1);
    if (BOPAllOwnedFields[VD].count(current) &&
        !BOPOwnedOwnedFields[VD].count(current)) {
      diags.push_back(
          OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidAssignFieldOfMoved,
                            fullFieldName + VD->getNameAsString()));
      break;
    }
  }
  if ((is(VD, Moved) || has(VD, Moved) || is(VD, Uninitialized) ||
       has(VD, Uninitialized)) &&
      diags.empty()) {
    diags.push_back(OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidUseOfMoved,
                                      VD->getNameAsString()));
  }

  if (BOPAllOwnedFields[VD].count(fullFieldName)) {
    // check condition 3
    if (BOPOwnedOwnedFields[VD].count(fullFieldName) && diags.empty()) {
      diags.push_back(
          OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidAssignFieldOfOwned,
                            VD->getNameAsString() + fullFieldName));
    }
    // calculate the fields with fullFieldName prefix
    auto allPrefixStrs =
        findPrefixStrings(BOPAllOwnedFields[VD], fullFieldName);
    auto ownedPrefixStrs =
        findPrefixStrings(BOPOwnedOwnedFields[VD], fullFieldName);
    if (!ownedPrefixStrs.empty() && diags.empty()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidAssignSubFieldOwned,
          VD->getNameAsString(), concatFields(VD, ownedPrefixStrs)));
    }
    if (!is(VD, Ownership::Status::Moved)) {
      if (BOPAllOwnedFields[VD].count(fullFieldName)) {
        BOPOwnedOwnedFields[VD].insert(fullFieldName);
      }
      // add allPrefixStrs to BOPOwnedOwnedFields
      for (auto str : allPrefixStrs) {
        BOPOwnedOwnedFields[VD].insert(str);
      }
    }
    if (BOPAllOwnedFields[VD].size() == BOPOwnedOwnedFields[VD].size()) {
      if (!is(VD, Ownership::Status::Owned) &&
          !is(VD, Ownership::Status::Moved)) {
        resetAll(VD);
        set(VD, Ownership::Status::Owned);
      }
    }
    if (BOPAllOwnedFields[VD].size() != BOPOwnedOwnedFields[VD].size()) {
      if (!is(VD, Ownership::Status::Owned) &&
          !is(VD, Ownership::Status::Moved)) {
        resetAll(VD);
        set(VD, Ownership::Status::PartialMoved);
      }
    }
  }

  return diags;
}

// if cast a `struct S * owned` variable to `void * owned`, we must ensure:
// 1. it is not moved or uninit
// 2. its owned fields are all moved
SmallVector<OwnershipDiagInfo, 3>
Ownership::OwnershipStatus::checkCastOPS(const VarDecl *VD,
                                         const SourceLocation &Loc) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  if (has(VD, Ownership::Status::Moved) || is(VD, Ownership::Status::Moved)) {
    diags.push_back(OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidCastMoved,
                                      VD->getNameAsString()));
  }
  if (has(VD, Uninitialized) || is(VD, Uninitialized)) {
    diags.push_back(OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidCastUninit,
                                      VD->getNameAsString()));
  }
  if (is(VD, PartialMoved)) {
    diags.push_back(OwnershipDiagInfo(
        Loc, OwnershipDiagKind::InvalidCastFieldOwned, VD->getNameAsString(),
        concatFields(VD, OPSOwnedOwnedFields[VD])));
  }
  if (!OPSOwnedOwnedFields[VD].empty() && diags.empty()) {
    diags.push_back(OwnershipDiagInfo(
        Loc, OwnershipDiagKind::InvalidCastFieldOwned, VD->getNameAsString(),
        concatFields(VD, OPSOwnedOwnedFields[VD])));
  }
  OPSOwnedOwnedFields[VD].clear();
  resetAll(VD);
  set(VD, Ownership::Status::Moved);

  return diags;
}

// if cast a `int * owned` variable to `void * owned`, we must ensure:
// 1. it is not moved
// 2. its owned fields are all moved
SmallVector<OwnershipDiagInfo, 3>
Ownership::OwnershipStatus::checkCastBOP(const VarDecl *VD,
                                         const SourceLocation &Loc) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  if (has(VD, Ownership::Status::Moved) || is(VD, Ownership::Status::Moved)) {
    diags.push_back(OwnershipDiagInfo(Loc, OwnershipDiagKind::InvalidCastMoved,
                                      VD->getNameAsString()));
  }
  if (!BOPOwnedOwnedFields[VD].empty() && diags.empty()) {
    diags.push_back(OwnershipDiagInfo(
        Loc, OwnershipDiagKind::InvalidCastFieldOwned, VD->getNameAsString(),
        concatFields(VD, BOPOwnedOwnedFields[VD])));
  }
  BOPOwnedOwnedFields[VD].clear();
  resetAll(VD);
  set(VD, Ownership::Status::Moved);

  return diags;
}

// TODO
SmallVector<OwnershipDiagInfo, 3> Ownership::OwnershipStatus::checkCastField(
    const VarDecl *VD, const SourceLocation &Loc, string fullFieldName) {
  SmallVector<OwnershipDiagInfo, 3> diags;

  if (OPSStatus.count(VD)) {
    if (is(VD, Ownership::Status::Moved) || has(VD, Ownership::Status::Moved)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidCastMoved, VD->getNameAsString()));
    }
    if (!OPSOwnedOwnedFields[VD].count(fullFieldName) && diags.empty()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidCastMoved,
          moveAsterisksToFront(VD->getNameAsString() + "." + fullFieldName)));
    }
    // calculate the fields with fullFieldName prefix
    auto allPrefixStrs =
        findPrefixStrings(OPSAllOwnedFields[VD], fullFieldName + ".");
    auto ownedPrefixStrs =
        findPrefixStrings(OPSOwnedOwnedFields[VD], fullFieldName + ".");
    if (!ownedPrefixStrs.empty() && diags.empty()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidCastFieldOwned,
          moveAsterisksToFront(VD->getNameAsString() + "." + fullFieldName),
          concatFields(VD, ownedPrefixStrs)));
    }
    if (OPSAllOwnedFields[VD].count(fullFieldName)) {
      OPSOwnedOwnedFields[VD].erase(fullFieldName);
    }
    // remove allPrefixStrs from OPSOwnedOwnedFields
    for (auto str : ownedPrefixStrs) {
      OPSOwnedOwnedFields[VD].erase(str);
    }
    if (OPSAllOwnedFields[VD].size() != OPSOwnedOwnedFields[VD].size()) {
      if (!is(VD, Ownership::Status::Moved)) {
        resetAll(VD);
        set(VD, Ownership::Status::PartialMoved);
      }
    }
    if (OPSOwnedOwnedFields[VD].empty() && !VD->getType()->getPointeeType()->isOwnedStructureType()) {
      if (!is(VD, Ownership::Status::Moved)) {
        resetAll(VD);
        set(VD, Ownership::Status::AllMoved);
      }
    }
  }

  if (SStatus.count(VD)) {
    if (!SOwnedOwnedFields[VD].count(fullFieldName)) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidCastMoved,
          moveAsterisksToFront(VD->getNameAsString() + "." + fullFieldName)));
    }
    // calculate the fields with fullFieldName prefix
    auto allPrefixStrs =
        findPrefixStrings(SAllOwnedFields[VD], fullFieldName + ".");
    auto ownedPrefixStrs =
        findPrefixStrings(SOwnedOwnedFields[VD], fullFieldName + ".");
    if (ownedPrefixStrs.size() != 0 && diags.empty()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::InvalidCastFieldOwned,
          moveAsterisksToFront(VD->getNameAsString() + "." + fullFieldName),
          concatFields(VD, ownedPrefixStrs)));
    }
    SOwnedOwnedFields[VD].erase(fullFieldName);
    for (auto str : ownedPrefixStrs) {
      SOwnedOwnedFields[VD].erase(str);
    }
  }

  return diags;
}

SmallVector<OwnershipDiagInfo, 3>
Ownership::OwnershipStatus::checkMemoryLeak(const VarDecl *VD,
                                            const SourceLocation &Loc) {
  SmallVector<OwnershipDiagInfo, 3> diags;
  // for a struct pointer owned variable,
  // the following two situations indicates that a memory leak has occurred:
  // 1. if OPSStatus[VD] is not MOVED or UNINITIALIZED, VD memory leak
  // 2. if OPSOwnedOwnedFields[VD] is not empty, VD's owned fields memory leak
  if (OPSStatus.count(VD)) {
    // situation 1
    if (!canAssign(VD)) {
      diags.push_back(OwnershipDiagInfo(Loc, OwnershipDiagKind::MemoryLeak,
                                        VD->getNameAsString()));
      // reset the state of VD, it's important in for/while
      resetAll(VD);
      set(VD, Ownership::Status::Moved);
    }
    // situation 2
    if (!OPSOwnedOwnedFields[VD].empty()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::FieldMemoryLeak, VD->getNameAsString(),
          concatFields(VD, OPSOwnedOwnedFields[VD])));
      OPSOwnedOwnedFields[VD].clear();
    }
  }

  // for a struct with owned fields,
  // the following situation indicates that a memory leak has occurred:
  // 1. if SOwnedOwnedFields[VD] is not empty, VD's owned fields memory leak
  if (SStatus.count(VD)) {
    if (!SOwnedOwnedFields[VD].empty()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::FieldMemoryLeak, VD->getNameAsString(),
          concatFields(VD, SOwnedOwnedFields[VD])));
      SOwnedOwnedFields[VD].clear();
    }
  }

  // for a basic owned pointer,
  // the following situation indicates that a memory leak has occurred:
  // 1. if BOPStatus[VD] is not MOVED, VD's memory leak
  // 2. if BOPOwnedOwnedFields[VD] is not empty, VD's owned fields memory leak
  if (BOPStatus.count(VD)) {
    // situation 1
    if (!canAssign(VD)) {
      diags.push_back(OwnershipDiagInfo(Loc, OwnershipDiagKind::MemoryLeak,
                                        VD->getNameAsString()));
      resetAll(VD);
      set(VD, Ownership::Status::Moved);
    }
    // situation 2
    if (!BOPOwnedOwnedFields[VD].empty()) {
      diags.push_back(OwnershipDiagInfo(
          Loc, OwnershipDiagKind::FieldMemoryLeak, VD->getNameAsString(),
          concatFields(VD, BOPOwnedOwnedFields[VD])));
      BOPOwnedOwnedFields[VD].clear();
    }
  }

  return diags;
}

//===----------------------------------------------------------------------===//
// Dataflow computation.
//===----------------------------------------------------------------------===//

namespace {
class TransferFunctions : public StmtVisitor<TransferFunctions> {
  OwnershipImpl &OS;
  Ownership::OwnershipStatus &stat;
  const CFGBlock *currentBlock;
  OwnershipDiagReporter &reporter;

  enum Operation { None, Assign, Move, GetAddr };
  mutable Operation op = Operation::None;

public:
  TransferFunctions(OwnershipImpl &os, Ownership::OwnershipStatus &Stat,
                    const CFGBlock *CurrentBlock,
                    OwnershipDiagReporter &reporter)
      : OS(os), stat(Stat), currentBlock(CurrentBlock), reporter(reporter) {}

  void VisitBinaryOperator(BinaryOperator *BO);
  void VisitCallExpr(CallExpr *CE);
  void VisitCStyleCastExpr(CStyleCastExpr *CSCE);
  void VisitDeclRefExpr(DeclRefExpr *DRE);
  void VisitDeclRefExpr(const DeclRefExpr *DRE, std::string fieldName);
  void VisitDeclStmt(DeclStmt *DS);
  void VisitInitListExpr(InitListExpr *ILE);
  void VisitMemberExpr(MemberExpr *ME);
  void VisitReturnStmt(ReturnStmt *RS);
  void VisitScopeEnd(VarDecl *VD, SourceLocation SL);
  void VisitStmt(Stmt *S);
  void VisitUnaryOperator(UnaryOperator *UO);

  void HandleDREAssign(const DeclRefExpr *DRE, std::string fullFieldName = "");
  void HandleDREUse(const DeclRefExpr *DRE, std::string fullFieldName = "");
};
} // namespace

void TransferFunctions::VisitStmt(Stmt *S) {
  for (auto *C : S->children()) {
    if (C) {
      Visit(C);
    }
  }
}

void TransferFunctions::VisitMemberExpr(MemberExpr *ME) {
  auto memberField = getMemberFullField(ME);

  // manipulate struct member expr assign
  if (op == Assign) {
    if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(memberField.first)) {
      HandleDREAssign(DRE, memberField.second);
    }
  }

  // manipulate struct member expr use
  if (op == Move || op == GetAddr) {
    if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(memberField.first))
      HandleDREUse(DRE, memberField.second);
  }
}

void TransferFunctions::VisitDeclRefExpr(DeclRefExpr *DRE) {
  if (op == Assign) {
    HandleDREAssign(DRE, "");
  }

  if (op == Move || op == GetAddr) {
    HandleDREUse(DRE, "");
  }
}

void TransferFunctions::VisitDeclRefExpr(const DeclRefExpr *DRE,
                                         string fieldName) {
  if (op == Assign) {
    HandleDREAssign(DRE, fieldName);
  }

  if (op == Move || op == GetAddr) {
    HandleDREUse(DRE, fieldName);
  }
}

void TransferFunctions::VisitUnaryOperator(UnaryOperator *UO) {
  string suffix;
  Expr *E = UO;
  while (UO->getOpcode() == UO_Deref) {
    if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(E)) {
      E = ICE->getSubExpr();
    } else if (UnaryOperator *uo = dyn_cast<UnaryOperator>(E)) {
      UO = uo;
      suffix += "*";
      E = UO->getSubExpr();
    } else {
      break;
    }
  }

  if (MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
    auto memberField = getMemberFullField(ME);
    if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(memberField.first)) {
      VisitDeclRefExpr(DRE, memberField.second + suffix);
      return;
    }
  }
  if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(E)) {
    VisitDeclRefExpr(DRE, suffix);
    return;
  }
  if (UO->getOpcode() == UO_AddrConstDeref ||
      UO->getOpcode() == UO_AddrMutDeref ||
      UO->getOpcode() == UO_AddrConst ||
      UO->getOpcode() == UO_AddrMut ||
      UO->getOpcode() == UO_AddrOf) {
    op = GetAddr;
  }
  Visit(UO->getSubExpr());
  op = None;
}

void TransferFunctions::VisitBinaryOperator(BinaryOperator *BO) {
  if (BO->getOpcode() == BO_Assign) {
    Expr *LHS = BO->getLHS();
    Expr *RHS = BO->getRHS();

    bool IsCall = IsCallExpr(RHS);
    if (!IsCall) {
      op = Move;
      Visit(RHS);
      op = None;
    }

    op = Assign;
    Visit(LHS);
    op = None;

    if (RHS->isNullExpr(OS.ctx)) {
      stat.setToNull(LHS);
    }
  }
}

void TransferFunctions::VisitCallExpr(CallExpr *CE) {
  for (auto it = CE->arg_begin(), ei = CE->arg_end(); it != ei; ++it) {
    bool IsCall = IsCallExpr(*it);
    if (!IsCall) {
      op = Move;
      Visit(*it);
      op = None;
    }
  }
}

void TransferFunctions::VisitCStyleCastExpr(CStyleCastExpr *CSCE) {
  if (CSCE->getType()->isVoidPointerType() &&
      CSCE->getType().isOwnedQualified()) {
    if (const ImplicitCastExpr *ICE =
            dyn_cast<ImplicitCastExpr>(CSCE->getSubExpr())) {
      // @code
      // (void * owned)s
      // @endcode
      if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())) {
        const VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl());
        if (stat.OPSStatus.count(VD)) {
          SmallVector<OwnershipDiagInfo, 3> diags =
              stat.checkCastOPS(VD, DRE->getLocation());
          reporter.addDiags(diags);
        }
        if (stat.BOPStatus.count(VD)) {
          SmallVector<OwnershipDiagInfo, 3> diags =
              stat.checkCastBOP(VD, DRE->getLocation());
          reporter.addDiags(diags);
        }
      }
      // @code
      // (void * owned)s->p
      // (void * owned)s.p
      // @endcode
      if (const MemberExpr *ME = dyn_cast<MemberExpr>(ICE->getSubExpr())) {
        auto memberField = getMemberFullField(ME);
        if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(memberField.first)) {
          SmallVector<OwnershipDiagInfo, 3> diags =
              stat.checkCastField(dyn_cast<VarDecl>(DRE->getDecl()),
                                  DRE->getLocation(), memberField.second);
          reporter.addDiags(diags);
        }
      }
    }
  } else {
    Visit(CSCE->getSubExpr());
  }
}

void TransferFunctions::VisitDeclStmt(DeclStmt *DS) {
  for (Decl *D : DS->decls()) {
    if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
      QualType VQT = VD->getType().getCanonicalType();
      if (IsTrackedType(VQT)) {
        stat.init(VD);
      }
      if (Expr *Init = VD->getInit()) {
        // if has init expr, change the status of VD from UNINIT to OWNED or NULL
        if (VQT->isPointerType() && VQT.isOwnedQualified()) {
          if (Init->isNullExpr(OS.ctx)) {
            stat.setToNull(VD);
          } else {
            stat.setToOwned(VD);
          }
        } else if (VQT->isRecordType() && VQT->hasOwnedFields() &&
                   isa<InitListExpr>(Init)) {
          stat.setToOwned(VD);
          if (stat.SStatus.count(VD)) {
            // If we init owned fields of a struct var with nullptr,
            // for example `struct S s = { .p = nullptr };`, here
            // we reset the status of s.p.
            auto RD = dyn_cast<RecordType>(VQT)->getDecl();
            auto ILE = dyn_cast<InitListExpr>(Init);
            Expr **Inits = ILE->getInits();
            for (const auto &FD : RD->fields()) {
              Expr *FieldInit = Inits[FD->getFieldIndex()];
              if (FieldInit->isNullExpr(OS.ctx)) {
                auto memberField = FD->getNameAsString();
                if (stat.SAllOwnedFields[VD].count(memberField)) {
                  stat.SOwnedOwnedFields[VD].erase(memberField);
                  stat.SNullOwnedFields[VD].insert(memberField);
                  auto allPrefixStrs =
                      findPrefixStrings(stat.SAllOwnedFields[VD], memberField + ".");
                  for (const string &str : allPrefixStrs) {
                    stat.SOwnedOwnedFields[VD].erase(str);
                    stat.SNullOwnedFields[VD].insert(str);
                  }
                }
              }
            }
            if (stat.SOwnedOwnedFields[VD].size() == 0) {
              stat.set(VD, Ownership::Status::AllMoved);
            } else if (stat.SAllOwnedFields[VD].size() != stat.SOwnedOwnedFields[VD].size()) {
              stat.set(VD, Ownership::Status::PartialMoved);
            }
          }
        } else {
          stat.setToOwned(VD);
        }
        // manipulate the init expr if it is not CallExpr
        bool IsCall = IsCallExpr(Init);
        if (!IsCall) {
          op = Move;
          Visit(Init);
          op = None;
        }
      }
    }
  }
}

void TransferFunctions::VisitInitListExpr(InitListExpr *ILE) {
  for (unsigned int i = 0, e = ILE->getNumInits(); i != e; ++i) {
    if (Expr *Init = ILE->getInit(i)) {
      if (!IsCallExpr(Init)) {
        op = Move;
        Visit(Init);
        op = None;
      }
    }
  }
}

void TransferFunctions::VisitReturnStmt(ReturnStmt *RS) {
  if (Expr *RV = RS->getRetValue()) {
    bool IsCall = IsCallExpr(RV);
    if (RV && !IsCall) {
      op = Move;
      Visit(RV);
      op = None;
    }
  }
}

void TransferFunctions::VisitScopeEnd(VarDecl *VD, SourceLocation SL) {
  // don't check memory leak of an owned struct type variable
  if (VD->getType().getTypePtr()->isOwnedStructureType())
    return;
  SmallVector<OwnershipDiagInfo, 3> diags = stat.checkMemoryLeak(VD, SL);
  reporter.addDiags(diags);
}

void TransferFunctions::HandleDREAssign(const DeclRefExpr *DRE,
                                        string fullFieldName) {
  // for a DeclRefExpr assign, there is 6 situations:
  // 1. assign a struct owned pointer as a whole, i.e. fullFieldName = ""
  // 2. assign a struct owned pointer's field, i.e. fullFieldName != ""
  // 3. assign a struct as a whole
  // 4. assign a struct's owned field
  // 5. assign a basic owned pointer as a whole
  // 6. assign a basic owned pointer's owned field
  if (const VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
    // situation 1 and 2
    if (stat.OPSStatus.count(VD)) {
      if (fullFieldName == "") {
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkOPSAssign(VD, DRE->getLocation());
        reporter.addDiags(diags);
      } else if (fullFieldName == "*") {
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkOPSAssignStar(VD, DRE->getLocation());
        reporter.addDiags(diags);
      } else {
        if (fullFieldName[fullFieldName.size() - 1] == '*') {
          fullFieldName[fullFieldName.size() - 1] = '.';
          if (stat.OPSAllOwnedFields[VD].count(fullFieldName.substr(0, fullFieldName.size() - 1))) {
            SmallVector<OwnershipDiagInfo, 3> diags =
                stat.checkOPSFieldAssign(VD, DRE->getLocation(), fullFieldName);
            reporter.addDiags(diags);
          }
          fullFieldName[fullFieldName.size() - 1] = '*';
        }
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkOPSFieldAssign(VD, DRE->getLocation(), fullFieldName);
        reporter.addDiags(diags);
      }
    }

    // situation 3 and 4
    if (stat.SStatus.count(VD)) {
      if (fullFieldName == "") {
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkSAssign(VD, DRE->getLocation());
        reporter.addDiags(diags);
      } else {
        if (fullFieldName[fullFieldName.size() - 1] == '*') {
          fullFieldName[fullFieldName.size() - 1] = '.';
          if (stat.SAllOwnedFields[VD].count(fullFieldName.substr(0, fullFieldName.size() - 1))) {
            SmallVector<OwnershipDiagInfo, 3> diags =
                stat.checkSFieldAssign(VD, DRE->getLocation(), fullFieldName);
            reporter.addDiags(diags);
          }
          fullFieldName[fullFieldName.size() - 1] = '*';
        }
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkSFieldAssign(VD, DRE->getLocation(), fullFieldName);
        reporter.addDiags(diags);
      }
    }

    // situation 5 and 6
    if (stat.BOPStatus.count(VD)) {
      if (fullFieldName == "") {
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkBOPAssign(VD, DRE->getLocation());
        reporter.addDiags(diags);
      } else {
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkBOPFieldAssign(VD, DRE->getLocation(), fullFieldName);
        reporter.addDiags(diags);
      }
    }
  }
}

void TransferFunctions::HandleDREUse(const DeclRefExpr *DRE,
                                     string fullFieldName) {
  // for a DeclRefExpr use, there is 4 situations:
  // 1. use a struct owned pointer as a whole, i.e. fullFieldName = ""
  // 2. use a struct owned pointer's field, i.e. fullFieldName != ""
  // 3. use a struct as a whole
  // 4. use a struct's owned field
  // 5. use a basic owned pointer as a whole
  // 6. use a basic owned pointer's owned field
  if (const VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
    // situation 1 and 2
    if (stat.OPSStatus.count(VD)) {
      if (fullFieldName == "") {
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkOPSUse(VD, DRE->getLocation(), op == GetAddr);
        reporter.addDiags(diags);
      } else if (fullFieldName == "*") {
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkOPSUse(VD, DRE->getLocation(), op == GetAddr, true);
        reporter.addDiags(diags);
      } else {
        if (fullFieldName[fullFieldName.size() - 1] == '*') {
          fullFieldName[fullFieldName.size() - 1] = '.';
          if (stat.OPSAllOwnedFields[VD].count(fullFieldName.substr(0, fullFieldName.size() - 1))) {
            SmallVector<OwnershipDiagInfo, 3> diags = stat.checkOPSFieldUse(
                VD, DRE->getLocation(), fullFieldName, op == GetAddr);
            reporter.addDiags(diags);
          }
          fullFieldName[fullFieldName.size() - 1] = '*';
        }
        SmallVector<OwnershipDiagInfo, 3> diags = stat.checkOPSFieldUse(
            VD, DRE->getLocation(), fullFieldName, op == GetAddr);
        reporter.addDiags(diags);
      }
    }

    // situation 3 and 4
    if (stat.SStatus.count(VD)) {
      if (fullFieldName == "") {
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkSUse(VD, DRE->getLocation(), op == GetAddr);
        reporter.addDiags(diags);
      } else {
        if (fullFieldName[fullFieldName.size() - 1] == '*') {
          fullFieldName[fullFieldName.size() - 1] = '.';
          if (stat.SAllOwnedFields[VD].count(fullFieldName.substr(0, fullFieldName.size() - 1))) {
            SmallVector<OwnershipDiagInfo, 3> diags = stat.checkSFieldUse(
                VD, DRE->getLocation(), fullFieldName, op == GetAddr);
            reporter.addDiags(diags);
          }
          fullFieldName[fullFieldName.size() - 1] = '*';
        }
        SmallVector<OwnershipDiagInfo, 3> diags = stat.checkSFieldUse(
            VD, DRE->getLocation(), fullFieldName, op == GetAddr);
        reporter.addDiags(diags);
      }
    }

    // situation 5 and 6
    if (stat.BOPStatus.count(VD)) {
      if (fullFieldName == "") {
        SmallVector<OwnershipDiagInfo, 3> diags =
            stat.checkBOPUse(VD, DRE->getLocation(), op == GetAddr);
        reporter.addDiags(diags);
      } else {
        SmallVector<OwnershipDiagInfo, 3> diags = stat.checkBOPFieldUse(
            VD, DRE->getLocation(), fullFieldName, op == GetAddr);
        reporter.addDiags(diags);
      }
    }
  }
}

void OwnershipImpl::MaybeSetNull(const CFGBlock *block,
                                 Ownership::OwnershipStatus &status) {
  if (block->pred_empty())
    return;
  const CFGBlock *pred = *block->pred_rbegin();
  if (pred == nullptr) {
    return;
  }
  if (const IfStmt *IS = dyn_cast_or_null<IfStmt>(pred->getTerminatorStmt())) {
    if (const BinaryOperator *BO = dyn_cast<BinaryOperator>(IS->getCond())) {
      if (BO->getRHS()->isNullExpr(ctx)) {
        if (const ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())) {
          if (BO->getOpcode() == BO_EQ) {
            if (*pred->succ_begin() == block) // block is True branch.
              status.setToNull(ICE->getSubExpr());
          } else if (BO->getOpcode() == BO_NE) {
            if (*(pred->succ_begin() + 1) == block) // block is False branch.
              status.setToNull(ICE->getSubExpr());
          }
        }
      }
    }
  }
}

Ownership::OwnershipStatus
OwnershipImpl::runOnBlock(const CFGBlock *block,
                          Ownership::OwnershipStatus status,
                          OwnershipDiagReporter &reporter) {
  MaybeSetNull(block, status);

  TransferFunctions TF(*this, status, block, reporter);

  for (CFGBlock::const_iterator it = block->begin(), ei = block->end();
       it != ei; ++it) {
    const CFGElement &elem = *it;

    if (elem.getAs<CFGStmt>()) {
      const Stmt *S = elem.castAs<CFGStmt>().getStmt();
      if (isa<DeclStmt>(S) || isa<CallExpr>(S) ||
          (isa<BinaryOperator>(S) &&
           dyn_cast<BinaryOperator>(S)->isAssignmentOp()) ||
          isa<ReturnStmt>(S)) {
        TF.Visit(const_cast<Stmt *>(S));
      }
    }

    if (elem.getAs<CFGScopeEnd>()) {
      const Stmt *S = elem.castAs<CFGScopeEnd>().getTriggerStmt();
      const VarDecl *VD = elem.castAs<CFGScopeEnd>().getVarDecl();
      TF.VisitScopeEnd(const_cast<VarDecl *>(VD), S->getEndLoc());
    }
  }

  return status;
}

void clang::runOwnershipAnalysis(const FunctionDecl &fd, const CFG &cfg,
                                 AnalysisDeclContext &ac,
                                 OwnershipDiagReporter &reporter,
                                 ASTContext &ctx) {
  // The analysis currently has scalability issues for very large CFGs.
  // Bail out if it looks too large.
  if (cfg.getNumBlockIDs() > 300000)
    return;

  OwnershipImpl *OS = new OwnershipImpl(ac, ctx);

  // Proceed with the worklist.
  ForwardDataflowWorklist worklist(cfg, ac);

  // Mark all owned parameter Owned at the entry
  const CFGBlock *entry = &cfg.getEntry();
  for (ParmVarDecl *PVD : fd.parameters()) {
    if (IsTrackedType(PVD->getType())) {
      if (const VarDecl *VD = dyn_cast<VarDecl>(PVD)) {
        OS->blocksEndStatus[entry].init(VD);
        OS->blocksEndStatus[entry].setToOwned(VD);
      }
    }
  }

  for (const CFGBlock *B : cfg.const_reverse_nodes())
    if (B != entry && !B->pred_empty())
      worklist.enqueueBlock(B);

  while (const CFGBlock *block = worklist.dequeue()) {
    Ownership::OwnershipStatus &preVal = OS->blocksBeginStatus[block];

    // meet operator
    Ownership::OwnershipStatus val;
    for (CFGBlock::const_pred_iterator it = block->pred_begin(),
                                       ei = block->pred_end();
         it != ei; ++it) {
      if (const CFGBlock *pred = *it) {
        val = OS->merge(val, OS->blocksEndStatus[pred]);
      }
    }

    OS->blocksEndStatus[block] = OS->runOnBlock(block, val, reporter);

    if (preVal.equals(val))
      continue;

    preVal = val;

    // Enqueue the value to the successors.
    worklist.enqueueSuccessors(block);
  }
  bool isDestructor = false;
  if (auto md = dyn_cast<BSCMethodDecl>(&fd)) {
    isDestructor = md->isDestructor();
  }
  // check ownership rules of function parameters
  const CFGBlock *exit = &cfg.getExit();
  for (ParmVarDecl *PVD : fd.parameters()) {
    if (const VarDecl *VD = dyn_cast<VarDecl>(PVD)) {
      // don't check memory leak of an owned struct type variable
      bool isOwnedStructType =
          (PVD->getType().getCanonicalType()->isOwnedStructureType() ||
           PVD->getType()
               .getCanonicalType()
               ->isOwnedTemplateSpecializationType());
      if (isOwnedStructType && !isDestructor) {
        continue;
      }

      SmallVector<OwnershipDiagInfo, 3> diags =
          OS->blocksEndStatus[exit].checkMemoryLeak(
              VD, fd.getSourceRange().getEnd());
      reporter.addDiags(diags);
    }
  }

  delete OS;
}

#endif // ENABLE_BSC