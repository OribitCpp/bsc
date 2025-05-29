//===- BSCNullabilityCheck.cpp - Nullability Check for Source CFGs -*- BSC--//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements BSC Pointer Nullability Check for source-level CFGs.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/Analysis/Analyses/BSC/BSCNullabilityCheck.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CFG.h"
#include "clang/Analysis/FlowSensitive/DataflowWorklist.h"
#include "llvm/ADT/DenseMap.h"
#include "clang/AST/ParentMap.h"

using namespace clang;
using namespace std;

// DefNullability is determined when a pointer is declared:
//   1. has nullability specifier, DefNullability depends on nullability
//   specifier.
//   2. has no nullability specifier, DefNullability depends on type:
//      1) raw pointer is nullable by default,
//      2) owned or borrow pointer is nonnull by default.
// Pointer with nullable DefNullability have PathNullability,
// which will change with control flow.
using StatusVD = llvm::DenseMap<VarDecl *, NullabilityKind>;
using FieldPath = std::pair<VarDecl *, std::string>;
using StatusFP = std::map<FieldPath, NullabilityKind>;

class NullabilityCheckImpl {
public:
  llvm::DenseMap<const CFGBlock *, StatusVD> BlocksBeginStatusVD;
  llvm::DenseMap<const CFGBlock *, StatusVD> BlocksEndStatusVD;

  llvm::DenseMap<const CFGBlock *, StatusFP> BlocksBeginStatusFP;
  llvm::DenseMap<const CFGBlock *, StatusFP> BlocksEndStatusFP;
  // For branch statement with condition, such as IfStmt, WhileStmt,
  // true branch and else branch may have different status.
  // For example:
  // @code
  //     int *p = nullptr;
  //     if (p != nullptr) {
  //         *p = 5;   // p is NonNull, so deref p is Ok
  //     } else {
  //         *p = 10;  // p is Nullable, so deref p is forbidden
  //     }
  // @endcode
  // CFG is:
  //        B4(has condition as terminitor)
  //    true /      \ false
  //        B3      B2
  //          \    /
  //            B1
  // BlocksConditionStatus records condition status:
  // Key is current BB, value is condition status passed from pred BB to current
  // BB, for this example, BlocksConditionStatusVD will be:
  // B3 : { B4 : p NonNull }  B2 : { B4 : p Nullable }
  llvm::DenseMap<
      const CFGBlock *,
      llvm::DenseMap<const CFGBlock *, std::pair<VarDecl *, NullabilityKind>>>
      BlocksConditionStatusVD;
  llvm::DenseMap<
      const CFGBlock *,
      llvm::DenseMap<const CFGBlock *, std::pair<FieldPath, NullabilityKind>>>
      BlocksConditionStatusFP;

  StatusVD mergeVD(StatusVD statusA, StatusVD statusB);
  StatusFP mergeFP(StatusFP statusA, StatusFP statusB);

  std::pair<StatusVD, StatusFP>
  runOnBlock(const CFGBlock *block, StatusVD statusVD, StatusFP statusFP,
             NullabilityCheckDiagReporter &reporter, ASTContext &ctx,
             const FunctionDecl &fd, ParentMap &PM);
  void initStatus(const CFG &cfg, ASTContext &ctx);

  NullabilityCheckImpl()
      : BlocksBeginStatusVD(0), BlocksEndStatusVD(0), BlocksBeginStatusFP(0),
        BlocksEndStatusFP(0), BlocksConditionStatusVD(0),
        BlocksConditionStatusFP(0) {}
};

//===----------------------------------------------------------------------===//
// Dataflow computation.
//===----------------------------------------------------------------------===//
namespace {
class TransferFunctions : public StmtVisitor<TransferFunctions> {
  NullabilityCheckImpl &NCI;
  const CFGBlock *Block;
  StatusVD &CurrStatusVD;
  StatusFP &CurrStatusFP;
  NullabilityCheckDiagReporter &Reporter;
  ASTContext &Ctx;
  const FunctionDecl &Fd;
  ParentMap &PM;

public:
  TransferFunctions(NullabilityCheckImpl &nci, const CFGBlock *block,
                    StatusVD &statusVD, StatusFP &statusFP,
                    NullabilityCheckDiagReporter &reporter, ASTContext &ctx,
                    const FunctionDecl &fd, ParentMap &pm)
      : NCI(nci), Block(block), CurrStatusVD(statusVD), CurrStatusFP(statusFP),
        Reporter(reporter), Ctx(ctx), Fd(fd), PM(pm) {}

  bool IsStmtInSafeZone(Stmt *S);
  bool ShouldReportNullPtrError(Stmt *S);
  void VisitDeclStmt(DeclStmt *S);
  void HandleVarDeclInit(DeclStmt *DS, VarDecl *VD);
  void HandlePointerInit(DeclStmt *DS, VarDecl *VD);
  void HandleStructInit(DeclStmt *DS, VarDecl *VD);
  void HandleFieldInit(DeclStmt *DS, VarDecl *VD, FieldDecl *FD, Expr *FieldInit);
  void VisitBinaryOperator(BinaryOperator *BO);
  void VisitUnaryOperator(UnaryOperator *UO);
  void VisitMemberExpr(MemberExpr *ME);
  void VisitCallExpr(CallExpr *CE);
  void VisitReturnStmt(ReturnStmt *RS);
  void VisitCStyleCastExpr(CStyleCastExpr *CSCE);
  NullabilityKind getExprPathNullability(Expr *E);
  void PassConditionStatusToSuccBlocks(Stmt *Cond);
};
} // namespace

static NullabilityKind getDefNullability(QualType QT, ASTContext &Ctx) {
  QualType CanQT = QT.getCanonicalType();
  if (CanQT->isPointerType()) {
    Optional<NullabilityKind> Kind = QT->getNullability(Ctx);
    if (Kind && (*Kind == NullabilityKind::NonNull ||
                 *Kind == NullabilityKind::Nullable)) {
      return *Kind;
    } else if (CanQT.isOwnedQualified() || CanQT.isBorrowQualified()) {
      return NullabilityKind::NonNull;
    } else // Raw Pointer is nullable by default.
      return NullabilityKind::Nullable;
  }
  return NullabilityKind::Unspecified;
}

static void VisitMEForFieldPath(Expr *E, FieldPath &FP) {
  if (auto ME = dyn_cast<MemberExpr>(E)) {
    if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
      FP.second = "." + FD->getNameAsString() + FP.second;
      VisitMEForFieldPath(ME->getBase(), FP);
    }
  } else if (auto DRE = dyn_cast<DeclRefExpr>(E)) {
    if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl()))
      FP.first = VD;
  } else if (auto ICE = dyn_cast<ImplicitCastExpr>(E)) {
    VisitMEForFieldPath(ICE->getSubExpr(), FP);
  } else if (auto PE = dyn_cast<ParenExpr>(E)) {
    VisitMEForFieldPath(PE->getSubExpr(), FP);
  }
}

static VarDecl *getVarDeclFromExpr(Expr *E) {
  if (auto DRE = dyn_cast<DeclRefExpr>(E)) {
    if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl()))
      return VD;
  } else if (auto ICE = dyn_cast<ImplicitCastExpr>(E)) {
    return getVarDeclFromExpr(ICE->getSubExpr());
  } else if (auto PE = dyn_cast<ParenExpr>(E)) {
    return getVarDeclFromExpr(PE->getSubExpr());
  }
  return nullptr;
}

static MemberExpr *getMemberExprFromExpr(Expr *E) {
  if (auto ME = dyn_cast<MemberExpr>(E)) {
    return ME;
  } else if (auto ICE = dyn_cast<ImplicitCastExpr>(E)) {
    return getMemberExprFromExpr(ICE->getSubExpr());
  } else if (auto PE = dyn_cast<ParenExpr>(E)) {
    return getMemberExprFromExpr(PE->getSubExpr());
  }
  return nullptr;
}

static CallExpr *getCallExprFromExpr(Expr *E) {
  if (auto CE = dyn_cast<CallExpr>(E)) {
    return CE;
  } else if (auto ICE = dyn_cast<ImplicitCastExpr>(E)) {
    return getCallExprFromExpr(ICE->getSubExpr());
  } else if (auto PE = dyn_cast<ParenExpr>(E)) {
    return getCallExprFromExpr(PE->getSubExpr());
  }
  return nullptr;
}

// We can get PathNullability for these exprs:
//   1. int *p = nullptr;   // nullptr is NullExpr
//   2. int *p = foo();     // foo() is CallExpr
//   3. int *p = &a;        // &a is UnaryOperator
//   4. int *p = p1;        // p1 is VarDecl
//   5. int *p = s.p;       // s.p is MemberExpr
//   6. int *p = a == 1 ? nullptr : &a; // ConditionOperator
NullabilityKind TransferFunctions::getExprPathNullability(Expr *E) {
  QualType QT = E->getType();
  QualType CanQT = QT.getCanonicalType();
  if (CanQT->isPointerType()) {
    if (E->isNullExpr(Ctx))
      return NullabilityKind::Nullable;
    if (auto CE = getCallExprFromExpr(E))
      return getDefNullability(CE->getType(), Ctx);
    if (auto CSCE = dyn_cast<CStyleCastExpr>(E))
      return getDefNullability(CSCE->getTypeAsWritten(), Ctx);
    if (auto UO = dyn_cast<UnaryOperator>(E)) {
      UnaryOperator::Opcode Op = UO->getOpcode();
      if (Op == UO_AddrOf || Op == UO_AddrMut || Op == UO_AddrConst ||
          Op == UO_AddrMutDeref || Op == UO_AddrConstDeref)
        return NullabilityKind::NonNull;
    }
    if (VarDecl *VD = getVarDeclFromExpr(E)) {
      NullabilityKind NK = getDefNullability(VD->getType(), Ctx);
      if (NK == NullabilityKind::NonNull)
        return NullabilityKind::NonNull;
      else if (NK == NullabilityKind::Nullable && CurrStatusVD.count(VD))
        return CurrStatusVD[VD];
    }
    if (MemberExpr *ME = getMemberExprFromExpr(E)) {
      if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
        NullabilityKind NK = getDefNullability(FD->getType(), Ctx);
        if (NK == NullabilityKind::NonNull)
          return NullabilityKind::NonNull;
        else if (NK == NullabilityKind::Nullable) {
          FieldPath FP;
          VisitMEForFieldPath(ME, FP);
          if (CurrStatusFP.count(FP))
            return CurrStatusFP[FP];
        }
      }
    }
    if (ConditionalOperator *CO = dyn_cast<ConditionalOperator>(E)) {
      NullabilityKind LHSNK = getExprPathNullability(CO->getLHS());
      NullabilityKind RHSNK = getExprPathNullability(CO->getRHS());
      if (LHSNK == NullabilityKind::Nullable ||
          RHSNK == NullabilityKind::Nullable)
        return NullabilityKind::Nullable;
      else if (LHSNK == NullabilityKind::NonNull ||
               RHSNK == NullabilityKind::NonNull)
        return NullabilityKind::NonNull;
    }
  }
  // For no-pointer type, we treat it as Unspecified.
  return NullabilityKind::Unspecified;
}

bool TransferFunctions::IsStmtInSafeZone(Stmt *S) {
  if (!S)
    return false;
  const Stmt *ParentStmt = PM.getParent(S);
  while (ParentStmt) {
    if (auto *CS = dyn_cast<CompoundStmt>(ParentStmt)) {
      SafeZoneSpecifier SafeZoneSpec = CS->getCompSafeZoneSpecifier();
      if (SafeZoneSpec == SZ_Safe) {
        return true;
      } else if (SafeZoneSpec == SZ_Unsafe) {
        return false;
      }
    }
    ParentStmt = PM.getParent(ParentStmt);
  }
  return Fd.getSafeZoneSpecifier() == SZ_Safe;
}

bool TransferFunctions::ShouldReportNullPtrError(Stmt *S) {
  LangOptions::NullCheckZone CheckZone = Ctx.getLangOpts().getNullabilityCheck();
  if (CheckZone == LangOptions::NC_ALL) {
    return true;
  }
  return IsStmtInSafeZone(S);
}

void TransferFunctions::VisitDeclStmt(DeclStmt *DS) {
  for (Decl *D : DS->decls())
    if (VarDecl *VD = dyn_cast<VarDecl>(D))
      if (VD->getInit())
        HandleVarDeclInit(DS, VD);
}

void TransferFunctions::HandleVarDeclInit(DeclStmt *DS, VarDecl *VD) {
  QualType VQT = VD->getType();
  if (VQT->isPointerType())
    HandlePointerInit(DS, VD);
  else if (VQT->isRecordType())
    HandleStructInit(DS, VD);
}

// Init a pointer variable
void TransferFunctions::HandlePointerInit(DeclStmt *DS, VarDecl *VD) {
  NullabilityKind LHSKind = getDefNullability(VD->getType(), Ctx);
  NullabilityKind RHSKind = getExprPathNullability(VD->getInit());
  if (LHSKind == NullabilityKind::NonNull) {
    // NonNull pointer cannot be assigned by expr
    // whose PathNullability is nullable.
    if (RHSKind == NullabilityKind::Nullable && ShouldReportNullPtrError(DS)) {
      NullabilityCheckDiagInfo DI(VD->getLocation(),
                                  NonnullAssignedByNullable);
      Reporter.addDiagInfo(DI);
    }
  } else if (CurrStatusVD.count(VD))
    // Here we update PathNullability of nullable pointer.
    CurrStatusVD[VD] = RHSKind;
}

// Init a struct variable with pointer fields.
void TransferFunctions::HandleStructInit(DeclStmt *DS, VarDecl *VD) {
  auto RecTy = dyn_cast<RecordType>(VD->getType().getCanonicalType());
  if (RecordDecl *RD = RecTy->getDecl()) {
    if (auto InitListE = dyn_cast<InitListExpr>(VD->getInit())) {
      // Init by InitListExpr, such as `struct S s = { .a = &local };`
      Expr **Inits = InitListE->getInits();
      for (FieldDecl *FD : RD->fields())
        if (FD->getType()->isPointerType())
          HandleFieldInit(DS, VD, FD, Inits[FD->getFieldIndex()]);
    }
  }
}

void TransferFunctions::HandleFieldInit(DeclStmt *DS, VarDecl *VD, FieldDecl *FD, Expr *FieldInit) {
  NullabilityKind LHSKind = getDefNullability(FD->getType(), Ctx);
  NullabilityKind RHSKind = getExprPathNullability(FieldInit);
  if (LHSKind == NullabilityKind::NonNull) {
    if (RHSKind == NullabilityKind::Nullable && ShouldReportNullPtrError(DS)) {
      NullabilityCheckDiagInfo DI(FieldInit->getBeginLoc(), NonnullAssignedByNullable);
      Reporter.addDiagInfo(DI);
    }
  } else {
    FieldPath FP(VD, "." + FD->getNameAsString());
    if (CurrStatusFP.count(FP))
      CurrStatusFP[FP] = RHSKind;
  }
}

void TransferFunctions::VisitBinaryOperator(BinaryOperator *BO) {
  if (BO->isAssignmentOp()) {
    Expr *LHS = BO->getLHS();
    QualType LHSQT = LHS->getType();
    if (LHSQT.getCanonicalType()->isPointerType()) {
      NullabilityKind RHSKind = getExprPathNullability(BO->getRHS());
      if (VarDecl *VD = getVarDeclFromExpr(LHS)) {
        NullabilityKind LHSKind = getDefNullability(VD->getType(), Ctx);
        if (LHSKind == NullabilityKind::NonNull) {
          // NonNull pointer cannot be assigned by expr
          // whose PathNullability is nullable.
          if (RHSKind == NullabilityKind::Nullable && ShouldReportNullPtrError(BO)) {
            NullabilityCheckDiagInfo DI(BO->getBeginLoc(),
                                        NonnullAssignedByNullable);
            Reporter.addDiagInfo(DI);
          }
        } else if (CurrStatusVD.count(VD)) {
          // Here we update PathNullability of nullable pointer.
          CurrStatusVD[VD] = RHSKind;
        }
      } else if (MemberExpr *ME = getMemberExprFromExpr(LHS)) {
        if (FieldDecl *FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
          NullabilityKind LHSKind = getDefNullability(FD->getType(), Ctx);
          if (LHSKind == NullabilityKind::NonNull) {
            if (RHSKind == NullabilityKind::Nullable && ShouldReportNullPtrError(BO)) {
              NullabilityCheckDiagInfo DI(ME->getBeginLoc(),
                                          NonnullAssignedByNullable);
              Reporter.addDiagInfo(DI);
            }
          } else {
            FieldPath FP;
            VisitMEForFieldPath(ME, FP);
            if (CurrStatusFP.count(FP))
              CurrStatusFP[FP] = RHSKind;
          }
        }
      }
    }
  }
}

// NonNull parameter cannot take Nullable pointer as argument.
void TransferFunctions::VisitCallExpr(CallExpr *CE) {
  if (FunctionDecl *FD = CE->getDirectCallee()) {
    for (unsigned i = 0; i < FD->getNumParams(); i++) {
      ParmVarDecl *PVD = FD->getParamDecl(i);
      if (getDefNullability(PVD->getType(), Ctx) == NullabilityKind::NonNull) {
        Expr *ArgE = CE->getArg(i);
        if (getExprPathNullability(ArgE) == NullabilityKind::Nullable && ShouldReportNullPtrError(CE)) {
          NullabilityCheckDiagInfo DI(ArgE->getBeginLoc(),
                                      PassNullableArgument);
          Reporter.addDiagInfo(DI);
        }
      }
    }
  }
}

// *p, &mut *p, &const *p is not allowed when p has nullable PathNullability.
void TransferFunctions::VisitUnaryOperator(UnaryOperator *UO) {
  UnaryOperator::Opcode Op = UO->getOpcode();
  if (Op == UO_Deref || Op == UO_AddrMutDeref || Op == UO_AddrConstDeref) {
    if (getExprPathNullability(UO->getSubExpr()) == NullabilityKind::Nullable && ShouldReportNullPtrError(UO)) {
      NullabilityCheckDiagInfo DI(UO->getBeginLoc(),
                                  NullablePointerDereference);
      Reporter.addDiagInfo(DI);
    }
  }
}

// p->a is not allowed when p has nullable PathNullability.
void TransferFunctions::VisitMemberExpr(MemberExpr *ME) {
  if (ME->isArrow()) {
    if (getExprPathNullability(ME->getBase()) == NullabilityKind::Nullable && ShouldReportNullPtrError(ME)) {
      NullabilityCheckDiagInfo DI(ME->getBeginLoc(),
                                  NullablePointerAccessMember);
      Reporter.addDiagInfo(DI);
    }
  }
}

// (int *_Nonnull)p, (int *borrow)p, (int *owned)p is not allowed
// when p has nullable PathNullability.
void TransferFunctions::VisitCStyleCastExpr(CStyleCastExpr *CSCE) {
  if (getDefNullability(CSCE->getTypeAsWritten(), Ctx) == NullabilityKind::NonNull) {
    if (getExprPathNullability(CSCE->getSubExpr()) == NullabilityKind::Nullable &&
        ShouldReportNullPtrError(CSCE)) {
      NullabilityCheckDiagInfo DI(CSCE->getBeginLoc(),
                                  NullableCastNonnull);
      Reporter.addDiagInfo(DI);
    }
  }
}

// If function return type is NonNull, cannot return pointer
// which has nullable PathNullability.
void TransferFunctions::VisitReturnStmt(ReturnStmt *RS) {
  Expr *RV = RS->getRetValue();
  if (!RV)
    return;
  if (getDefNullability(Fd.getReturnType(), Ctx) == NullabilityKind::NonNull) {
    if (getExprPathNullability(RV) == NullabilityKind::Nullable && ShouldReportNullPtrError(RS)) {
      NullabilityCheckDiagInfo DI(RV->getBeginLoc(), ReturnNullable);
      Reporter.addDiagInfo(DI);
    }
  }
}

// This function handles condition expression and
// pass the conditions to successor block.
void TransferFunctions::PassConditionStatusToSuccBlocks(Stmt *Cond) {
  CFGBlock::const_succ_iterator it = Block->succ_begin();
  if (const CFGBlock *TrueBlock = *it) {
    it++;
    if (const CFGBlock *FalseBlock = *it) {
      // When building CFG, if a block has a condition as terminitor,
      // the successors has certain order, for example:
      //    B4(has condition as terminitor)
      //   /  \
      //  B3  B2
      // The first successor of B4 must be true branch,
      // and the second successor of B4 must be false branch.
      // Here we only handle terminators with two successors.
      if (auto BO = dyn_cast<BinaryOperator>(Cond)) {
        // Condition expr is BinaryOperator, such as:
        // if (p != nullptr), if (s.p != nullptr), if (p == nullptr), if (s.p !=
        // nullptr), ...
        if (BO->isEqualityOp() && BO->getRHS()->isNullExpr(Ctx)) {
          Expr *LHS = BO->getLHS();
          if (VarDecl *VD = getVarDeclFromExpr(LHS)) {
            if (getDefNullability(VD->getType(), Ctx) ==
                NullabilityKind::Nullable) {
              NullabilityKind TrueKind = BO->getOpcode() == BO_EQ
                                             ? NullabilityKind::Nullable
                                             : NullabilityKind::NonNull;
              NullabilityKind FalseKind = BO->getOpcode() == BO_EQ
                                              ? NullabilityKind::NonNull
                                              : NullabilityKind::Nullable;
              NCI.BlocksConditionStatusVD[TrueBlock][Block] =
                  std::pair<VarDecl *, NullabilityKind>(VD, TrueKind);
              NCI.BlocksConditionStatusVD[FalseBlock][Block] =
                  std::pair<VarDecl *, NullabilityKind>(VD, FalseKind);
            }
          } else if (MemberExpr *ME = getMemberExprFromExpr(LHS)) {
            if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
              if (getDefNullability(FD->getType(), Ctx) ==
                  NullabilityKind::Nullable) {
                NullabilityKind TrueKind = BO->getOpcode() == BO_EQ
                                               ? NullabilityKind::Nullable
                                               : NullabilityKind::NonNull;
                NullabilityKind FalseKind = BO->getOpcode() == BO_EQ
                                                ? NullabilityKind::NonNull
                                                : NullabilityKind::Nullable;
                FieldPath FP;
                VisitMEForFieldPath(ME, FP);
                NCI.BlocksConditionStatusFP[TrueBlock][Block] =
                    std::pair<FieldPath, NullabilityKind>(FP, TrueKind);
                NCI.BlocksConditionStatusFP[FalseBlock][Block] =
                    std::pair<FieldPath, NullabilityKind>(FP, FalseKind);
              }
            }
          }
        }
      } else if (auto ICE = dyn_cast<ImplicitCastExpr>(Cond)) {
        // Condition expr is ImplicitCastExpr, such as: if (p), if (s.p), ...
        if (VarDecl *VD = getVarDeclFromExpr(ICE)) {
          if (getDefNullability(VD->getType(), Ctx) ==
              NullabilityKind::Nullable) {
            NCI.BlocksConditionStatusVD[TrueBlock][Block] =
                std::pair<VarDecl *, NullabilityKind>(VD,
                                                      NullabilityKind::NonNull);
            NCI.BlocksConditionStatusVD[FalseBlock][Block] =
                std::pair<VarDecl *, NullabilityKind>(
                    VD, NullabilityKind::Nullable);
          }
        } else if (MemberExpr *ME = getMemberExprFromExpr(ICE)) {
          if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
            if (getDefNullability(FD->getType(), Ctx) ==
                NullabilityKind::Nullable) {
              FieldPath FP;
              VisitMEForFieldPath(ME, FP);
              NCI.BlocksConditionStatusFP[TrueBlock][Block] =
                  std::pair<FieldPath, NullabilityKind>(
                      FP, NullabilityKind::NonNull);
              NCI.BlocksConditionStatusFP[FalseBlock][Block] =
                  std::pair<FieldPath, NullabilityKind>(
                      FP, NullabilityKind::Nullable);
            }
          }
        }
      } else if (auto UO = dyn_cast<UnaryOperator>(Cond)) {
        // Condition expr is UnaryOperator, such as:
        // if (!p), if (!s.p), ...
        if (UO->getOpcode() == UO_LNot) {
          if (VarDecl *VD = getVarDeclFromExpr(UO->getSubExpr())) {
            if (getDefNullability(VD->getType(), Ctx) ==
                NullabilityKind::Nullable) {
              NCI.BlocksConditionStatusVD[TrueBlock][Block] =
                  std::pair<VarDecl *, NullabilityKind>(
                      VD, NullabilityKind::Nullable);
              NCI.BlocksConditionStatusVD[FalseBlock][Block] =
                  std::pair<VarDecl *, NullabilityKind>(
                      VD, NullabilityKind::NonNull);
            }
          } else if (MemberExpr *ME = getMemberExprFromExpr(UO->getSubExpr())) {
            if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
              if (getDefNullability(FD->getType(), Ctx) ==
                  NullabilityKind::Nullable) {
                FieldPath FP;
                VisitMEForFieldPath(ME, FP);
                NCI.BlocksConditionStatusFP[TrueBlock][Block] =
                    std::pair<FieldPath, NullabilityKind>(
                        FP, NullabilityKind::Nullable);
                NCI.BlocksConditionStatusFP[FalseBlock][Block] =
                    std::pair<FieldPath, NullabilityKind>(
                        FP, NullabilityKind::NonNull);
              }
            }
          }
        }
      }
    }
  }
}

// Traverse all blocks of cfg to collect all nullable pointers used,
// including local and global variable and parameters.
// Init PathNullability of these pointers by Nullable.
void NullabilityCheckImpl::initStatus(const CFG &cfg, ASTContext &ctx) {
  const CFGBlock *entry = &cfg.getEntry();
  for (const CFGBlock *B : cfg.const_nodes()) {
    if (B != entry && B != &cfg.getExit() && !B->succ_empty() &&
        !B->pred_empty()) {
      for (CFGBlock::const_iterator it = B->begin(), ei = B->end(); it != ei;
           ++it) {
        const CFGElement &elem = *it;
        if (elem.getAs<CFGStmt>()) {
          Stmt *S = const_cast<Stmt *>(elem.castAs<CFGStmt>().getStmt());
          if (auto DRE = dyn_cast<DeclRefExpr>(S)) {
            if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl()))
              if (getDefNullability(VD->getType(), ctx) ==
                  NullabilityKind::Nullable)
                BlocksEndStatusVD[entry][VD] = NullabilityKind::Nullable;
          } else if (auto ME = dyn_cast<MemberExpr>(S)) {
            if (FieldDecl *FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
              if (getDefNullability(FD->getType(), ctx) ==
                  NullabilityKind::Nullable) {
                FieldPath FP;
                VisitMEForFieldPath(ME, FP);
                BlocksEndStatusFP[entry][FP] = NullabilityKind::Nullable;
              }
            }
          }
        }
      }
    }
  }
}

StatusVD NullabilityCheckImpl::mergeVD(StatusVD statusA, StatusVD statusB) {
  if (statusA.empty())
    return statusB;
  for (auto NullabilityOfVD : statusB) {
    VarDecl *VD = NullabilityOfVD.first;
    NullabilityKind NK = NullabilityOfVD.second;
    if (statusA.count(VD)) {
      statusA[VD] = NK == NullabilityKind::Nullable ? NullabilityKind::Nullable
                                                    : statusA[VD];
    } else {
      statusA[VD] = NK;
    }
  }
  return statusA;
}

StatusFP NullabilityCheckImpl::mergeFP(StatusFP statusA, StatusFP statusB) {
  if (statusA.empty())
    return statusB;
  for (auto NullabilityOfFP : statusB) {
    FieldPath FP = NullabilityOfFP.first;
    NullabilityKind NK = NullabilityOfFP.second;
    if (statusA.count(FP)) {
      statusA[FP] = NK == NullabilityKind::Nullable ? NullabilityKind::Nullable
                                                    : statusA[FP];
    } else {
      statusA[FP] = NK;
    }
  }
  return statusA;
}

std::pair<StatusVD, StatusFP>
NullabilityCheckImpl::runOnBlock(const CFGBlock *block, StatusVD statusVD,
                                 StatusFP statusFP,
                                 NullabilityCheckDiagReporter &reporter,
                                 ASTContext &ctx, const FunctionDecl &fd, ParentMap &PM) {
  TransferFunctions TF(*this, block, statusVD, statusFP, reporter, ctx, fd, PM);

  for (CFGBlock::const_iterator it = block->begin(), ei = block->end();
       it != ei; ++it) {
    const CFGElement &elem = *it;
    if (elem.getAs<CFGStmt>()) {
      const Stmt *S = elem.castAs<CFGStmt>().getStmt();
      TF.Visit(const_cast<Stmt *>(S));
    }
  }

  // Here we will handle the condition in IfStmt, or other branch stmts
  // which will change the nullability of VarDecl or FiledPath.
  if (const Stmt *TS = block->getTerminatorStmt()) {
    if (isa<IfStmt>(TS) || isa<WhileStmt>(TS) || isa<DoStmt>(TS) ||
        isa<BinaryOperator>(TS)) {
      const CFGElement &elem = *(block->rbegin());
      if (elem.getAs<CFGStmt>()) {
        const Stmt *S = elem.castAs<CFGStmt>().getStmt();
        TF.PassConditionStatusToSuccBlocks(const_cast<Stmt *>(S));
      }
    }
  }
  return std::make_pair(statusVD, statusFP);
}

void clang::runNullabilityCheck(const FunctionDecl &fd, const CFG &cfg,
                                AnalysisDeclContext &ac,
                                NullabilityCheckDiagReporter &reporter,
                                ASTContext &ctx) {
  // The analysis currently has scalability issues for very large CFGs.
  // Bail out if it looks too large.
  if (cfg.getNumBlockIDs() > 300000)
    return;

  NullabilityCheckImpl NCI;
  NCI.initStatus(cfg, ctx);

  // Proceed with the worklist.
  ForwardDataflowWorklist worklist(cfg, ac);
  const CFGBlock *entry = &cfg.getEntry();
  for (const CFGBlock *B : cfg.const_reverse_nodes())
    if (B != entry && !B->pred_empty())
      worklist.enqueueBlock(B);

  while (const CFGBlock *block = worklist.dequeue()) {
    StatusVD &preValVD = NCI.BlocksBeginStatusVD[block];
    StatusFP &preValFP = NCI.BlocksBeginStatusFP[block];
    StatusVD valVD;
    StatusFP valFP;
    for (CFGBlock::const_pred_iterator it = block->pred_begin(),
                                       ei = block->pred_end();
         it != ei; ++it) {
      if (const CFGBlock *pred = *it) {
        StatusVD predValVD = NCI.BlocksEndStatusVD[pred];
        if (NCI.BlocksConditionStatusVD.count(block)) {
          if (NCI.BlocksConditionStatusVD[block].count(pred)) {
            std::pair<VarDecl *, NullabilityKind> condition =
                NCI.BlocksConditionStatusVD[block][pred];
            predValVD[condition.first] = condition.second;
          }
        }
        valVD = NCI.mergeVD(valVD, predValVD);

        StatusFP predValFP = NCI.BlocksEndStatusFP[pred];
        if (NCI.BlocksConditionStatusFP.count(block)) {
          if (NCI.BlocksConditionStatusFP[block].count(pred)) {
            std::pair<FieldPath, NullabilityKind> condition =
                NCI.BlocksConditionStatusFP[block][pred];
            predValFP[condition.first] = condition.second;
          }
        }
        valFP = NCI.mergeFP(valFP, predValFP);
      }
    }

    std::pair<StatusVD, StatusFP> val =
        NCI.runOnBlock(block, valVD, valFP, reporter, ctx, fd, ac.getParentMap());
    NCI.BlocksEndStatusVD[block] = val.first;
    NCI.BlocksEndStatusFP[block] = val.second;
    if (preValVD == val.first && preValFP == val.second)
      continue;

    preValVD = val.first;
    preValFP = val.second;

    // Enqueue the value to the successors.
    worklist.enqueueSuccessors(block);
  }
}
#endif // ENABLE_BSC