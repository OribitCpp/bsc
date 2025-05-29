//===--- SemaDeclBSC.cpp - Semantic Analysis for Declarations
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

#include "TreeTransform.h"
#include "clang/AST/BSC/WalkerBSC.h"
#include "clang/Analysis/Analyses/BSC/BSCBorrowChecker.h"
#include "clang/Analysis/Analyses/BSC/BSCNullabilityCheck.h"
#include "clang/Analysis/Analyses/BSC/BSCOwnership.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Sema/Sema.h"

using namespace clang;
using namespace sema;

void Sema::CheckBSCConstexprFunction(FunctionDecl* FD) {
  assert(getLangOpts().BSC && FD->isConstexprSpecified());
  // BSC constexpr function can not be async.
  if (FD->isAsyncSpecified()) {
    Diag(FD->getBeginLoc(), diag::err_async_func_unsupported)
        << "constexpr";
  }
  // BSC constexpr function can not be variadic.
  if (FD->isVariadic()) {
    Diag(FD->getBeginLoc(), diag::err_constexpr_func_unsupported)
        << "variadic";
  }
  // The return type and parameter type of BSC constexpr function should be compile_time_calculated type.
  QualType RT = FD->getReturnType();
  if (!RT->isDependentType() && !RT->isBSCCalculatedTypeInCompileTime()) {
    Diag(FD->getBeginLoc(), diag::err_constexpr_func_unsupported_type) << RT;
  }
  for (ParmVarDecl* PVD: FD->parameters()) {
    QualType PT = PVD->getType();
    if (!PT->isDependentType() && !PT->isBSCCalculatedTypeInCompileTime()) {
      Diag(PVD->getLocation(), diag::err_constexpr_func_unsupported_type) << PT;
    }
  }
}

// The type of BSC constexpr variable should be compile_time_calculated type.
void Sema::CheckBSCConstexprVarType(VarDecl* VD) {
  assert(getLangOpts().BSC);
  QualType T = VD->getType();
  if (T->isDependentType())
    return;
  if (VD->isConstexpr() && !T->isBSCCalculatedTypeInCompileTime()) {
    Diag(VD->getLocation(), diag::err_constexpr_var_unsupported_type) << T;
    VD->setInvalidDecl();
    return;
  }
  if (FunctionDecl* FD = dyn_cast_or_null<FunctionDecl>(VD->getDeclContext())) {
    if (FD->isConstexpr() && !T->isBSCCalculatedTypeInCompileTime()) {
      Diag(VD->getLocation(), diag::err_constexpr_func_unsupported_type) << VD->getType();
      VD->setInvalidDecl();
      return;
    }
  }
}

bool HasDiffBorrorOrOwnedQualifiers(QualType LHSType, QualType RHSType) {
  if (LHSType.isOwnedQualified() != RHSType.isOwnedQualified()) {
    return true;
  }
  if (LHSType.isBorrowQualified() != RHSType.isBorrowQualified()) {
    return true;
  }
  if (LHSType->isPointerType() && RHSType->isPointerType()) {
    QualType LHSPType = LHSType->getPointeeType();
    QualType RHSPType = RHSType->getPointeeType();
    return HasDiffBorrorOrOwnedQualifiers(LHSPType, RHSPType);
  }
  return false;
}

bool Sema::HasDiffBorrowOrOwnedParamsTypeAtBothFunction(QualType LHS,
                                                        QualType RHS) {
  const FunctionProtoType *LSHFuncType = LHS->getAs<FunctionProtoType>();
  const FunctionProtoType *RSHFuncType = RHS->getAs<FunctionProtoType>();
  if (!LSHFuncType || !RSHFuncType) {
    return false;
  }

  QualType LHSRetType = LSHFuncType->getReturnType();
  QualType RHSRetType = RSHFuncType->getReturnType();
  if (HasDiffBorrorOrOwnedQualifiers(LHSRetType, RHSRetType)) {
    return true;
  }
  if (LSHFuncType->getNumParams() != RSHFuncType->getNumParams()) {
    return true;
  }
  for (unsigned i = 0; i < LSHFuncType->getNumParams(); i++) {
    QualType LHSParType = LSHFuncType->getParamType(i).getUnqualifiedType();
    QualType RHSParType = RSHFuncType->getParamType(i).getUnqualifiedType();
    if (HasDiffBorrorOrOwnedQualifiers(LHSParType, RHSParType)) {
      return true;
    }
  }
  return false;
}

// Return true if any memory safe features are found in a FunctionDecl.
// Qualifiers: owned, borrow, fat
// AddrOp: &mut, &const
bool Sema::FindSafeFeatures(const FunctionDecl* FnDecl) {
  if (!FnDecl) return false;
  SafeFeatureFinder finder;
  if (finder.FindOwnedOrBorrow(const_cast<FunctionDecl*>(FnDecl))) {
    return true;
  }
  return false;
}

bool Sema::HasSafeZoneInCompoundStmt(const CompoundStmt* CompStmt) {
  if (!CompStmt) {
    return false;
  }
  for (const Stmt *child: CompStmt->children()) {
    if (auto *CompChild = dyn_cast<CompoundStmt>(child)) {
      if (CompChild->getCompSafeZoneSpecifier() == SZ_Safe) {
        return true;
      }
      if (HasSafeZoneInCompoundStmt(CompChild)) {
        return true;
      }
    }
  }
  return false;
}

bool Sema::HasSafeZoneInFunction(const FunctionDecl* FnDecl) {
  if (!FnDecl || !FnDecl->getBody()) {
    return false;
  }
  if (FnDecl->getSafeZoneSpecifier() == SZ_Safe) {
    return true;
  }
  CompoundStmt *FuncBody = cast<CompoundStmt>(FnDecl->getBody());
  if (!FuncBody) {
    return false;
  }
  return HasSafeZoneInCompoundStmt(FuncBody);
}

/// BSC's dataflow analysis process is as follows:
/// ====================================================================
///                      __________________       ___________________
///                     |                  |     |                   |
/// FuncDecl--> CFG --> | NullabilityCheck | --> | OwnershipAnalysis | -->
///                     |__________________|     |___________________|
///       __________________
///      |                  |
///  --> |   BorrowCheck    | -->  FuncDecl  --> CodeGen
///      |__________________|
/// ====================================================================
void Sema::BSCDataflowAnalysis(const Decl *D, bool EnableOwnershipCheck,
                               bool EnableNullabilityCheck) {
  AnalysisDeclContext AC(/* AnalysisDeclContextManager */ nullptr, D);

  // TODO: understand how these parameters affect the CFG.
  AC.getCFGBuildOptions().PruneTriviallyFalseEdges = true;
  AC.getCFGBuildOptions().AddEHEdges = false;
  AC.getCFGBuildOptions().AddInitializers = true;
  AC.getCFGBuildOptions().AddImplicitDtors = true;
  AC.getCFGBuildOptions().AddTemporaryDtors = true;
  AC.getCFGBuildOptions().AddScopes = true;
  AC.getCFGBuildOptions().BSCMode = true;
  AC.getCFGBuildOptions().setAllAlwaysAdd();

  const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(D);

  // If D does not use memory safety features like "owned, borrow, &mut, &const",
  // we should not do borrow checking.
  bool RequireBorrowCheck = LangOpts.BSC ? FindSafeFeatures(FD) : false;
  // nullability-check happens in mode: {SafeOnly, All}.
  // For SafeOnly, do not build cfg when there is no SafeZone in Function.
  bool RequireNullabilityCheck = EnableNullabilityCheck;
  if (getLangOpts().getNullabilityCheck() == LangOptions::NC_SAFE) {
    if(HasSafeZoneInFunction(FD)) {
      RequireNullabilityCheck = EnableNullabilityCheck;
    } else {
      RequireNullabilityCheck = false;
    }
  }
  bool RequireCFGAnalysis = RequireNullabilityCheck || RequireBorrowCheck;
  if (RequireCFGAnalysis && FD && AC.getCFG()) { // Only build the CFG when needed.
    // Step one: Run NullabilityCheck
    unsigned NumNullabilityCheckErrorsInCurrFD = 0;
    if (RequireNullabilityCheck) {
      NullabilityCheckDiagReporter NullabilityCheckReporter(*this);
      runNullabilityCheck(*FD, *AC.getCFG(), AC, NullabilityCheckReporter,
                          Context);
      NullabilityCheckReporter.flushDiagnostics();
      NumNullabilityCheckErrorsInCurrFD =
          NullabilityCheckReporter.getNumErrors();

    }
    // Step two: Run ownership analysis when there is no nullability errors in
    // current function.
    bool DoBorrowCheck = EnableOwnershipCheck & RequireBorrowCheck;
    if (DoBorrowCheck && !NumNullabilityCheckErrorsInCurrFD) {
      OwnershipDiagReporter OwnershipReporter(*this);
      runOwnershipAnalysis(*FD, *AC.getCFG(), AC, OwnershipReporter, Context);
      OwnershipReporter.flushDiagnostics();
      // Step three: Run borrow checker when there is no other ownership errors and
      // nullability in current function.
      if (!OwnershipReporter.getNumErrors()) {
        BSCBorrowChecker(const_cast<FunctionDecl *>(FD));
      }
    }
  }
}

struct ReplaceNodesMap {
  /// When we replace an AST node `p` with an AST node `q`, we use `q` as value
  /// and use `p` as key and insert into the map.
  /// When we execute BorrowCheckerEpilogue, when we find the key of an AST
  /// node, we replace it with the corresponding value.
  llvm::DenseMap<Expr *, Expr *> replacedExprsMap;
  llvm::DenseMap<Stmt *, Stmt *> replacedStmtsMap;

  bool Contains(Expr *E) const {
    return replacedExprsMap.find(E) != replacedExprsMap.end();
  }

  bool Contains(Stmt *S) const {
    return replacedStmtsMap.find(S) != replacedStmtsMap.end();
  }

  void Insert(Expr *Key, Expr *Value) { replacedExprsMap[Key] = Value; }

  void Insert(Stmt *Key, Stmt *Value) { replacedStmtsMap[Key] = Value; }

  Expr *Get(Expr *Key) { return replacedExprsMap[Key]; }

  Stmt *Get(Stmt *Key) { return replacedStmtsMap[Key]; }
};

/// Before running borrow checker, introduce some temporary variables to adjust
/// FunctionDecl in the AST, replacing nested function calls and complex
/// expressions.
///
/// The complexity for AST nodes presents significant challenges for
/// implementing the borrow checker. For example, scenarios like `foo(bar())`
/// are not convenient for analysis. To handle such cases, we use a temporary
/// variable to store the return value of `bar()` before passing it as an
/// argument to `foo()`, ensuring a semantically equivalent transformation.
class BorrowCheckerPrologue : public TreeTransform<BorrowCheckerPrologue> {
  typedef TreeTransform<BorrowCheckerPrologue> BaseTransform;

  FunctionDecl *FD;
  llvm::SmallVector<Stmt *, 8> Stmts;
  bool NeedToReplace = false; // A flag indicating whether to create a temporary
                              // variable to replace the current CallExpr.
  unsigned TempVarCounter = 0;

  ReplaceNodesMap &replacedNodesMap;

  // Replace function call expression or unary operator expression with a
  // temporary variable, and return the corresponding DeclRefExpr.
  DeclRefExpr *ReplaceWithTemporaryVariable(Expr *E) {
    std::string Name = "_borrowck_tmp_" + std::to_string(TempVarCounter++);
    VarDecl *VD = VarDecl::Create(
        getSema().Context, FD, SourceLocation(), SourceLocation(),
        &getSema().Context.Idents.get(Name), E->getType(), nullptr, SC_None);
    VD->setInit(E);
    DeclStmt *DS = new (getSema().Context)
        DeclStmt(DeclGroupRef(VD), SourceLocation(), SourceLocation());
    Stmts.push_back(DS);
    return DeclRefExpr::Create(getSema().Context, NestedNameSpecifierLoc(),
                               SourceLocation(), VD, false, E->getBeginLoc(),
                               E->getType(), VK_LValue);
  }

  CompoundStmt *GetOrWrapWithCompoundStmt(Stmt *S) {
    if (isa<CompoundStmt>(S))
      return dyn_cast<CompoundStmt>(S);
    return CompoundStmt::Create(SemaRef.Context, S, FPOptionsOverride(),
                                S->getBeginLoc(), S->getEndLoc());
  }

public:
  BorrowCheckerPrologue(Sema &SemaRef, FunctionDecl *FD,
                        ReplaceNodesMap &replacedNodesMap)
      : BaseTransform(SemaRef), FD(FD), replacedNodesMap(replacedNodesMap) {}

  // Don't redo semantic analysis to ensure that AST nodes are not rebuilt to
  // affect destructor insertion.
  bool AlwaysRebuild() { return false; }

  void applyTransform() {
    StmtResult Res = BaseTransform::TransformStmt(FD->getBody());
    FD->setBody(Res.get());
  }

  StmtResult TransformCaseStmt(CaseStmt *CS) {
    CS->setLHS(getDerived().TransformExpr(CS->getLHS()).get());
    if (Expr *RHS = CS->getRHS())
      CS->setRHS(getDerived().TransformExpr(RHS).get());
    if (Stmt *Sub = CS->getSubStmt()) {
      CompoundStmt *SubBody = GetOrWrapWithCompoundStmt(Sub);
      StmtResult ResSub = getDerived().TransformStmt(SubBody);
      CS->setSubStmt(ResSub.get());
      replacedNodesMap.Insert(ResSub.get(), Sub);
    }
    return CS;
  }

  StmtResult TransformCompoundStmt(CompoundStmt *CS) {
    return TransformCompoundStmt(CS, false);
  }

  // Transform each stmt in the CompoundStmt.
  StmtResult TransformCompoundStmt(CompoundStmt *CS, bool IsStmtExpr) {
    if (CS == nullptr)
      return CS;

    llvm::SmallVector<Stmt *, 8> PrevStmts = Stmts;
    llvm::SmallVector<Stmt *, 8> CurStmts;
    Stmts = CurStmts;
    // Traverse and transform all statements in the compound statement.
    for (Stmt *S : CS->body()) {
      StmtResult Res = BaseTransform::TransformStmt(S);
      Stmts.push_back(Res.getAs<Stmt>());
    }
    CompoundStmt *NewCS = CompoundStmt::Create(
        SemaRef.Context, Stmts, FPOptionsOverride(), CS->getLBracLoc(),
        CS->getRBracLoc(), CS->getSafeSpecifier(), CS->getSafeSpecifierLoc(),
        CS->getCompSafeZoneSpecifier());
    Stmts = PrevStmts;
    replacedNodesMap.Insert(NewCS, CS);

    return NewCS;
  }

  StmtResult TransformDeclStmt(DeclStmt *DS) {
    for (Decl *D : DS->decls()) {
      if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
        if (VD->hasInit()) {
          getDerived().TransformExpr(VD->getInit());
        }
      }
    }

    return DS;
  }

  StmtResult TransformDefaultStmt(DefaultStmt *DS) {
    if (Stmt *Sub = DS->getSubStmt()) {
      CompoundStmt *SubBody = GetOrWrapWithCompoundStmt(Sub);
      StmtResult ResSub = getDerived().TransformStmt(SubBody);
      DS->setSubStmt(ResSub.get());
      replacedNodesMap.Insert(ResSub.get(), Sub);
    }
    return DS;
  }

  StmtResult TransformDoStmt(DoStmt *DS) {
    Stmt *Body = DS->getBody();
    CompoundStmt *CSBody = GetOrWrapWithCompoundStmt(Body);
    StmtResult ResBody = getDerived().TransformStmt(CSBody);
    DS->setBody(ResBody.get());
    replacedNodesMap.Insert(ResBody.get(), Body);
    DS->setCond(getDerived().TransformExpr(DS->getCond()).get());

    return DS;
  }

  StmtResult TransformForStmt(ForStmt *FS) {
    FS->setInit(getDerived().TransformStmt(FS->getInit()).get());
    FS->setCond(getDerived().TransformExpr(FS->getCond()).get());
    FS->setInc(getDerived().TransformExpr(FS->getInc()).get());
    Stmt *Body = FS->getBody();
    CompoundStmt *CSBody = GetOrWrapWithCompoundStmt(Body);
    StmtResult ResBody = getDerived().TransformStmt(CSBody);
    FS->setBody(ResBody.get());
    replacedNodesMap.Insert(ResBody.get(), Body);

    return FS;
  }

  StmtResult TransformIfStmt(IfStmt *IS) {
    Expr *Cond = IS->getCond();
    ExprResult ResCond = getDerived().TransformExpr(Cond);
    IS->setCond(ResCond.get());

    Stmt *Then = IS->getThen();
    CompoundStmt *CSThen = GetOrWrapWithCompoundStmt(Then);
    StmtResult ResThen = getDerived().TransformStmt(CSThen);
    IS->setThen(ResThen.get());
    replacedNodesMap.Insert(ResThen.get(), Then);

    if (Stmt *Else = IS->getElse()) {
      CompoundStmt *CSElse = GetOrWrapWithCompoundStmt(Else);
      StmtResult ResElse = getDerived().TransformStmt(CSElse);
      IS->setElse(ResElse.get());
      replacedNodesMap.Insert(ResElse.get(), Else);
    }

    return IS;
  }

  StmtResult TransformReturnStmt(ReturnStmt *RS) {
    if (!RS->getRetValue())
      return RS;

    bool Old = NeedToReplace;
    NeedToReplace = true;
    ExprResult Res = getDerived().TransformExpr(RS->getRetValue());
    Expr *E = Res.get();
    if (CallExpr *CE = dyn_cast_or_null<CallExpr>(E)) {
      DeclRefExpr *DRE = ReplaceWithTemporaryVariable(CE);
      CastKind Kind =
          DRE->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
      ImplicitCastExpr *ICE =
          ImplicitCastExpr::Create(getSema().Context, DRE->getType(), Kind, DRE,
                                   nullptr, VK_PRValue, FPOptionsOverride());
      replacedNodesMap.Insert(ICE, CE);
      RS->setRetValue(ICE);
      return RS;
    }
    if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
      DeclRefExpr *DRE = ReplaceWithTemporaryVariable(UO);
      CastKind Kind =
          DRE->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
      ImplicitCastExpr *ICE =
          ImplicitCastExpr::Create(getSema().Context, DRE->getType(), Kind, DRE,
                                   nullptr, VK_PRValue, FPOptionsOverride());
      replacedNodesMap.Insert(ICE, UO);
      RS->setRetValue(ICE);
      return RS;
    }
    RS->setRetValue(E);
    NeedToReplace = Old;
    return RS;
  }

  StmtResult TransformSwitchStmt(SwitchStmt *SS) {
    SS->setCond(getDerived().TransformExpr(SS->getCond()).get());
    SS->setBody(getDerived().TransformStmt(SS->getBody()).get());
    return SS;
  }

  StmtResult TransformWhileStmt(WhileStmt *WS) {
    WS->setCond(getDerived().TransformExpr(WS->getCond()).get());
    Stmt *Body = WS->getBody();
    CompoundStmt *CSBody = GetOrWrapWithCompoundStmt(Body);
    StmtResult ResBody = getDerived().TransformStmt(CSBody);
    WS->setBody(ResBody.get());
    replacedNodesMap.Insert(ResBody.get(), Body);

    return WS;
  }

  ExprResult TransformBinaryOperator(BinaryOperator *BO) {
    bool Old = NeedToReplace;
    NeedToReplace = true;
    ExprResult ResLHS = getDerived().TransformExpr(BO->getLHS());
    Expr *ELHS = ResLHS.get();
    if (CallExpr *CE = dyn_cast<CallExpr>(ELHS)) {
      DeclRefExpr *DRE = ReplaceWithTemporaryVariable(CE);
      CastKind Kind =
          DRE->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
      ELHS =
          ImplicitCastExpr::Create(getSema().Context, DRE->getType(), Kind, DRE,
                                   nullptr, VK_PRValue, FPOptionsOverride());
      replacedNodesMap.Insert(ELHS, CE);
    }
    BO->setLHS(ELHS);
    NeedToReplace = Old;
    ExprResult ResRHS = getDerived().TransformExpr(BO->getRHS());
    Expr *ERHS = ResRHS.get();
    if (BO->getOpcode() < BO_Assign) {
      if (CallExpr *CE = dyn_cast<CallExpr>(ERHS)) {
        DeclRefExpr *DRE = ReplaceWithTemporaryVariable(CE);
        CastKind Kind =
            DRE->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
        ERHS = ImplicitCastExpr::Create(getSema().Context, DRE->getType(), Kind,
                                        DRE, nullptr, VK_PRValue,
                                        FPOptionsOverride());
        replacedNodesMap.Insert(ERHS, CE);
      }
    }
    BO->setRHS(ERHS);
    return BO;
  }

  ExprResult TransformCallExpr(CallExpr *CE) {
    bool Old = NeedToReplace;
    for (unsigned i = 0; i < CE->getNumArgs(); ++i) {
      Expr *Arg = CE->getArg(i);
      NeedToReplace = true;
      ExprResult Res = getDerived().TransformExpr(Arg);
      Expr *E = Res.get();

      if (CallExpr *NestedCall = dyn_cast<CallExpr>(E)) {
        E = ReplaceWithTemporaryVariable(NestedCall);
        CastKind Kind =
            E->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
        E = ImplicitCastExpr::Create(getSema().Context, E->getType(), Kind, E,
                                     nullptr, VK_PRValue, FPOptionsOverride());
        replacedNodesMap.Insert(E, NestedCall);
      } else if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
        if (UO->getOpcode() >= UO_AddrMut &&
            UO->getOpcode() <= UO_AddrConstDeref) {
          E = ReplaceWithTemporaryVariable(UO);
          CastKind Kind =
              E->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
          E = ImplicitCastExpr::Create(getSema().Context, E->getType(), Kind, E,
                                       nullptr, VK_PRValue,
                                       FPOptionsOverride());
          replacedNodesMap.Insert(E, UO);
        }
      }
      CE->setArg(i, E);
    }
    NeedToReplace = Old;
    return CE;
  }

  ExprResult TransformCompoundLiteralExpr(CompoundLiteralExpr *CLE) {
    ExprResult Res = getDerived().TransformExpr(CLE->getInitializer());
    Expr *E = Res.get();
    CLE->setInitializer(E);
    return CLE;
  }

  ExprResult TransformCStyleCastExpr(CStyleCastExpr *CSCE) {
    ExprResult Res = getDerived().TransformExpr(CSCE->getSubExpr());
    Expr *E = Res.get();
    if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
      if (NeedToReplace) {
        E = ReplaceWithTemporaryVariable(CE);
        replacedNodesMap.Insert(E, CE);
      }
    } else if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
      if (NeedToReplace) {
        E = ReplaceWithTemporaryVariable(UO);
        replacedNodesMap.Insert(E, UO);
      }
    }
    CSCE->setSubExpr(E);
    return CSCE;
  }

  ExprResult TransformImplicitCastExpr(ImplicitCastExpr *ICE) {
    ExprResult Res = getDerived().TransformExpr(ICE->getSubExpr());
    Expr *E = Res.get();
    if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
      if (NeedToReplace) {
        DeclRefExpr *DRE = ReplaceWithTemporaryVariable(CE);
        replacedNodesMap.Insert(DRE, CE);
        ICE->setSubExpr(DRE);
        return ICE;
      }
    }
    ICE->setSubExpr(E);
    return ICE;
  }

  ExprResult TransformInitListExpr(InitListExpr *ILE) {
    for (unsigned i = 0; i < ILE->getNumInits(); ++i) {
      ExprResult Res = getDerived().TransformExpr(ILE->getInit(i));
      Expr *E = Res.get();
      if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
        E = ReplaceWithTemporaryVariable(CE);
        replacedNodesMap.Insert(E, CE);
      } else if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
        if (UO->getOpcode() >= UO_AddrMut &&
            UO->getOpcode() <= UO_AddrConstDeref) {
          E = ReplaceWithTemporaryVariable(UO);
          CastKind Kind =
              E->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
          ImplicitCastExpr *ICE = ImplicitCastExpr::Create(
              getSema().Context, E->getType(), Kind, E, nullptr, VK_PRValue,
              FPOptionsOverride());
          E = ICE;
          replacedNodesMap.Insert(E, UO);
        }
      }
      ILE->setInit(i, E);
    }
    return ILE;
  }

  ExprResult TransformMemberExpr(MemberExpr *ME) {
    ExprResult Res = getDerived().TransformExpr(ME->getBase());
    Expr *E = Res.get();
    if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
      E = ReplaceWithTemporaryVariable(CE);
      CastKind Kind =
          E->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
      E = ImplicitCastExpr::Create(getSema().Context, E->getType(), Kind, E,
                                   nullptr, VK_PRValue, FPOptionsOverride());
      replacedNodesMap.Insert(E, CE);
    }
    ME->setBase(E);
    return ME;
  }

  ExprResult TransformParenExpr(ParenExpr *PE) {
    ExprResult Res = getDerived().TransformExpr(PE->getSubExpr());
    Expr *E = Res.get();
    if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
      DeclRefExpr *DRE = ReplaceWithTemporaryVariable(E);
      CastKind Kind =
          DRE->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
      E = ImplicitCastExpr::Create(getSema().Context, DRE->getType(), Kind,
                                   DRE, nullptr, VK_PRValue,
                                   FPOptionsOverride());
      replacedNodesMap.Insert(E, CE);
    } else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(E)) {
      DeclRefExpr *DRE = ReplaceWithTemporaryVariable(E);
      CastKind Kind =
          DRE->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
      E = ImplicitCastExpr::Create(getSema().Context, DRE->getType(), Kind,
                                   DRE, nullptr, VK_PRValue,
                                   FPOptionsOverride());
      replacedNodesMap.Insert(E, BO);
    }
    PE->setSubExpr(E);

    return PE;
  }

  ExprResult TransformStmtExpr(StmtExpr *SE) {
    StmtResult Res = getDerived().TransformStmt(SE->getSubStmt());
    SE->setSubStmt(Res.getAs<CompoundStmt>());
    return SE;
  }

  ExprResult TransformUnaryOperator(UnaryOperator *UO) {
    ExprResult Res = getDerived().TransformExpr(UO->getSubExpr());
    Expr *E = Res.get();
    if (UO->getOpcode() == UO_Deref) {
      if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
        DeclRefExpr *DRE = ReplaceWithTemporaryVariable(E);
        CastKind Kind =
            DRE->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
        E = ImplicitCastExpr::Create(getSema().Context, DRE->getType(), Kind,
                                     DRE, nullptr, VK_PRValue,
                                     FPOptionsOverride());
        replacedNodesMap.Insert(E, CE);
      } else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(E)) {
        DeclRefExpr *DRE = ReplaceWithTemporaryVariable(E);
        CastKind Kind =
            DRE->getType()->getAsCXXRecordDecl() ? CK_NoOp : CK_LValueToRValue;
        E = ImplicitCastExpr::Create(getSema().Context, DRE->getType(), Kind,
                                     DRE, nullptr, VK_PRValue,
                                     FPOptionsOverride());
        replacedNodesMap.Insert(E, BO);
      }
    }
    UO->setSubExpr(E);
    return UO;
  }
};

/// After running borrow checker, restore the AST to its original form to avoid
/// any impact on other compiler phases caused by AST transformations.
class BorrowCheckerEpilogue : public TreeTransform<BorrowCheckerEpilogue> {
  typedef TreeTransform<BorrowCheckerEpilogue> BaseTransform;

  FunctionDecl *FD;
  ReplaceNodesMap &replacedNodesMap;

public:
  BorrowCheckerEpilogue(Sema &SemaRef, FunctionDecl *FD,
                        ReplaceNodesMap &replacedNodesMap)
      : BaseTransform(SemaRef), FD(FD), replacedNodesMap(replacedNodesMap) {}

  // Don't redo semantic analysis to ensure that AST nodes are not rebuilt to
  // affect destructor insertion.
  bool AlwaysRebuild() { return false; }

  void applyTransform() {
    StmtResult Res = BaseTransform::TransformStmt(FD->getBody());
    FD->setBody(Res.get());
  }

  StmtResult TransformCaseStmt(CaseStmt *CS) {
    CS->setLHS(getDerived().TransformExpr(CS->getLHS()).get());
    if (Expr *RHS = CS->getRHS())
      CS->setRHS(getDerived().TransformExpr(RHS).get());
    if (Stmt *Sub = CS->getSubStmt()) {
      if (replacedNodesMap.Contains(Sub)) {
        Sub = replacedNodesMap.Get(Sub);
      }
      StmtResult ResSub = getDerived().TransformStmt(Sub);
      CS->setSubStmt(ResSub.get());
    }
    return CS;
  }

  StmtResult TransformCompoundStmt(CompoundStmt *CS) {
    return TransformCompoundStmt(CS, false);
  }

  // Transform each stmt in the CompoundStmt.
  StmtResult TransformCompoundStmt(CompoundStmt *CS, bool IsStmtExpr) {
    if (CS == nullptr)
      return CS;

    if (replacedNodesMap.Contains(CS)) {
      CS = cast<CompoundStmt>(replacedNodesMap.Get(CS));
    }

    // Traverse and transform all statements in the compound statement.
    for (Stmt *S : CS->body()) {
      BaseTransform::TransformStmt(S);
    }

    return CS;
  }

  StmtResult TransformDeclStmt(DeclStmt *DS) {
    for (Decl *D : DS->decls()) {
      if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
        if (VD->hasInit()) {
          getDerived().TransformExpr(VD->getInit());
        }
      }
    }

    return DS;
  }

  StmtResult TransformDefaultStmt(DefaultStmt *DS) {
    if (Stmt *Sub = DS->getSubStmt()) {
      if (replacedNodesMap.Contains(Sub)) {
        Sub = replacedNodesMap.Get(Sub);
      }
      StmtResult ResSub = getDerived().TransformStmt(Sub);
      DS->setSubStmt(ResSub.get());
    }
    return DS;
  }

  StmtResult TransformDoStmt(DoStmt *DS) {
    Stmt *Body = DS->getBody();
    if (replacedNodesMap.Contains(Body)) {
      Body = replacedNodesMap.Get(Body);
    }
    StmtResult ResBody = getDerived().TransformStmt(Body);
    DS->setBody(ResBody.get());
    DS->setCond(getDerived().TransformExpr(DS->getCond()).get());

    return DS;
  }

  StmtResult TransformForStmt(ForStmt *FS) {
    FS->setInit(getDerived().TransformStmt(FS->getInit()).get());
    FS->setCond(getDerived().TransformExpr(FS->getCond()).get());
    FS->setInc(getDerived().TransformExpr(FS->getInc()).get());
    Stmt *Body = FS->getBody();
    if (replacedNodesMap.Contains(Body)) {
      Body = replacedNodesMap.Get(Body);
    }
    StmtResult ResBody = getDerived().TransformStmt(Body);
    FS->setBody(ResBody.get());

    return FS;
  }

  StmtResult TransformIfStmt(IfStmt *IS) {
    Expr *Cond = IS->getCond();
    ExprResult ResCond = getDerived().TransformExpr(Cond);
    IS->setCond(ResCond.get());

    Stmt *Then = IS->getThen();
    if (replacedNodesMap.Contains(Then)) {
      Then = replacedNodesMap.Get(Then);
    }
    StmtResult ResThen = getDerived().TransformStmt(Then);
    IS->setThen(ResThen.get());

    if (Stmt *Else = IS->getElse()) {
      if (replacedNodesMap.Contains(Else)) {
        Else = replacedNodesMap.Get(Else);
      }
      StmtResult ResElse = getDerived().TransformStmt(Else);
      IS->setElse(ResElse.get());
    }

    return IS;
  }

  StmtResult TransformReturnStmt(ReturnStmt *RS) {
    if (!RS->getRetValue())
      return RS;

    if (replacedNodesMap.Contains(RS->getRetValue())) {
      RS->setRetValue(replacedNodesMap.Get(RS->getRetValue()));
    }

    ExprResult Res = getDerived().TransformExpr(RS->getRetValue());
    Expr *E = Res.get();

    RS->setRetValue(E);
    return RS;
  }

  StmtResult TransformSwitchStmt(SwitchStmt *SS) {
    SS->setCond(getDerived().TransformExpr(SS->getCond()).get());
    SS->setBody(getDerived().TransformStmt(SS->getBody()).get());
    return SS;
  }

  StmtResult TransformWhileStmt(WhileStmt *WS) {
    WS->setCond(getDerived().TransformExpr(WS->getCond()).get());
    Stmt *Body = WS->getBody();
    if (replacedNodesMap.Contains(Body)) {
      Body = replacedNodesMap.Get(Body);
    }
    StmtResult Res = getDerived().TransformStmt(Body);
    WS->setBody(Res.get());

    return WS;
  }

  ExprResult TransformBinaryOperator(BinaryOperator *BO) {
    Expr *LHS = BO->getLHS();
    if (replacedNodesMap.Contains(LHS)) {
      LHS = replacedNodesMap.Get(LHS);
    }
    ExprResult ResLHS = getDerived().TransformExpr(LHS);
    BO->setLHS(ResLHS.get());
    Expr *RHS = BO->getRHS();
    if (replacedNodesMap.Contains(RHS)) {
      RHS = replacedNodesMap.Get(RHS);
    }
    ExprResult ResRHS = getDerived().TransformExpr(RHS);
    BO->setRHS(ResRHS.get());
    return BO;
  }

  ExprResult TransformCallExpr(CallExpr *CE) {
    for (unsigned i = 0; i < CE->getNumArgs(); ++i) {
      Expr *Arg = CE->getArg(i);
      if (replacedNodesMap.Contains(Arg)) {
        Arg = replacedNodesMap.Get(Arg);
      }
      ExprResult Res = getDerived().TransformExpr(Arg);
      Expr *E = Res.get();

      CE->setArg(i, E);
    }
    return CE;
  }

  ExprResult TransformCompoundLiteralExpr(CompoundLiteralExpr *CLE) {
    ExprResult Res = getDerived().TransformExpr(CLE->getInitializer());
    Expr *E = Res.get();
    CLE->setInitializer(E);
    return CLE;
  }

  ExprResult TransformCStyleCastExpr(CStyleCastExpr *CSCE) {
    Expr *Sub = CSCE->getSubExpr();
    if (replacedNodesMap.Contains(Sub)) {
      Sub = replacedNodesMap.Get(Sub);
    }
    ExprResult Res = getDerived().TransformExpr(Sub);
    CSCE->setSubExpr(Res.get());

    return CSCE;
  }

  ExprResult TransformImplicitCastExpr(ImplicitCastExpr *ICE) {
    Expr *Sub = ICE->getSubExpr();
    if (replacedNodesMap.Contains(Sub)) {
      Sub = replacedNodesMap.Get(Sub);
    }
    ExprResult Res = getDerived().TransformExpr(Sub);
    ICE->setSubExpr(Res.get());

    return ICE;
  }

  ExprResult TransformInitListExpr(InitListExpr *ILE) {
    for (unsigned i = 0; i < ILE->getNumInits(); ++i) {
      Expr *Init = ILE->getInit(i);
      if (replacedNodesMap.Contains(Init)) {
        Init = replacedNodesMap.Get(Init);
      }
      ExprResult Res = getDerived().TransformExpr(Init);
      ILE->setInit(i, Res.get());
    }

    return ILE;
  }

  ExprResult TransformMemberExpr(MemberExpr *ME) {
    Expr *Base = ME->getBase();
    if (replacedNodesMap.Contains(Base)) {
      Base = replacedNodesMap.Get(Base);
    }
    ExprResult Res = getDerived().TransformExpr(Base);
    ME->setBase(Res.get());

    return ME;
  }

  ExprResult TransformParenExpr(ParenExpr *PE) {
    Expr *Sub = PE->getSubExpr();
    if (replacedNodesMap.Contains(Sub)) {
      Sub = replacedNodesMap.Get(Sub);
    }
    ExprResult Res = getDerived().TransformExpr(Sub);
    PE->setSubExpr(Res.get());

    return PE;
  }

  ExprResult TransformStmtExpr(StmtExpr *SE) {
    StmtResult Res = getDerived().TransformStmt(SE->getSubStmt());
    SE->setSubStmt(Res.getAs<CompoundStmt>());
    return SE;
  }

  ExprResult TransformUnaryOperator(UnaryOperator *UO) {
    Expr *Sub = UO->getSubExpr();
    if (UO->getOpcode() == UO_Deref) {
      if (replacedNodesMap.Contains(Sub)) {
        Sub = replacedNodesMap.Get(Sub);
      }
    }
    ExprResult Res = getDerived().TransformExpr(Sub);
    UO->setSubExpr(Res.get());

    return UO;
  }
};

void Sema::BSCBorrowChecker(FunctionDecl *FD) {
  ReplaceNodesMap replacedNodesMap;
  BorrowCheckerPrologue BCP(*this, FD, replacedNodesMap);
  BCP.applyTransform();

  AnalysisDeclContext AC(/* AnalysisDeclContextManager */ nullptr, FD);
  AC.getCFGBuildOptions().PruneTriviallyFalseEdges = true;
  AC.getCFGBuildOptions().AddEHEdges = false;
  AC.getCFGBuildOptions().AddInitializers = true;
  AC.getCFGBuildOptions().AddImplicitDtors = true;
  AC.getCFGBuildOptions().AddTemporaryDtors = true;
  AC.getCFGBuildOptions().AddScopes = true;
  AC.getCFGBuildOptions().BSCMode = true;
  AC.getCFGBuildOptions().BSCBorrowCk = true;
  AC.getCFGBuildOptions()
      .setAlwaysAdd(Stmt::BinaryOperatorClass)
      .setAlwaysAdd(Stmt::BreakStmtClass)
      .setAlwaysAdd(Stmt::CompoundStmtClass)
      .setAlwaysAdd(Stmt::DeclStmtClass)
      .setAlwaysAdd(Stmt::DoStmtClass)
      .setAlwaysAdd(Stmt::ForStmtClass)
      .setAlwaysAdd(Stmt::IfStmtClass)
      .setAlwaysAdd(Stmt::ReturnStmtClass)
      .setAlwaysAdd(Stmt::SwitchStmtClass)
      .setAlwaysAdd(Stmt::WhileStmtClass);

  if (AC.getCFG()) {
#if DEBUG_PRINT
    AC.getCFG()->dump(LangOpts, true);
#endif
    borrow::BorrowDiagReporter Reporter(*this);
    borrow::runBorrowChecker(*FD, *AC.getCFG(), Context, Reporter);
  }

  BorrowCheckerEpilogue BCE(*this, FD, replacedNodesMap);
  BCE.applyTransform();
}

#endif