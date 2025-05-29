#if ENABLE_BSC

#include <stack>

#include "TreeTransform.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Sema/Scope.h"
#include "clang/Sema/Template.h"

using namespace clang;
using namespace sema;

static BSCMethodDecl *buildBSCMethodDecl(ASTContext &C, DeclContext *DC,
                                         SourceLocation StartLoc,
                                         SourceLocation NLoc, DeclarationName N,
                                         QualType T, TypeSourceInfo *TInfo,
                                         StorageClass SC, QualType ET) {
  // TODO: inline should be passed.
  BSCMethodDecl *NewDecl = BSCMethodDecl::Create(
      C, DC, StartLoc, DeclarationNameInfo(N, NLoc), T, TInfo, SC, false, false,
      ConstexprSpecKind::Unspecified, NLoc);
  return NewDecl;
}

bool IsVarDeclWithOwnedStructureType(VarDecl *VD) {
  const Type *VDType = VD->getType().getCanonicalType().getTypePtr();
  if (VDType->isOwnedStructureType() && !VD->hasGlobalStorage())
    return true;
  return false;
}

// Collect owned struct type field that has destructor.
std::stack<FieldDecl *> CollectInstanceFieldWithDestructor(RecordDecl *RD) {
  std::stack<FieldDecl *> OwnedStructFields;
  for (RecordDecl::field_iterator FieldIt = RD->field_begin();
       FieldIt != RD->field_end(); ++FieldIt) {
    const Type *FieldType = FieldIt->getType().getCanonicalType().getTypePtr();
    if (FieldType->isOwnedStructureType()) {
      RecordDecl *RD = cast<RecordType>(FieldType)->getDecl();
      if (RD->getBSCDestructor() && !RD->getBSCDestructor()->isInvalidDecl()) {
        OwnedStructFields.push(*FieldIt);
      }
    }
  }
  return OwnedStructFields;
}

BSCMethodDecl *Sema::getOrInsertBSCDestructor(RecordDecl *RD) {
  BSCMethodDecl *Destructor;
  if (RD->getBSCDestructor() == nullptr) {
    assert(RD->isOwnedDecl());
    QualType FuncRetType = getASTContext().VoidTy;
    QualType ParamType = getASTContext().getRecordType(RD);
    if (const InjectedClassNameType *ICT =
            dyn_cast<const InjectedClassNameType>(ParamType)) {
      ParamType = ICT->getInjectedSpecializationType();
    }
    ParamType.addOwned();
    SmallVector<QualType, 1> ParamTys;
    ParamTys.push_back(ParamType);
    QualType FuncType =
        getASTContext().getFunctionType(FuncRetType, ParamTys, {});
    DeclarationName Name = Context.DeclarationNames.getCXXDestructorName(
        Context.getCanonicalType(Context.getTypeDeclType(RD)));

    TypeSourceInfo *TInfo =
        Context.getTrivialTypeSourceInfo(FuncType, RD->getEndLoc());
    FunctionProtoTypeLoc ProtoLoc =
        TInfo->getTypeLoc().IgnoreParens().castAs<FunctionProtoTypeLoc>();
    Destructor = buildBSCMethodDecl(
        getASTContext(), RD, RD->getEndLoc(), RD->getEndLoc(), Name, FuncType,
        TInfo, SC_None, RD->getTypeForDecl()->getCanonicalTypeInternal());
    SmallVector<ParmVarDecl *, 1> ParmVarDecls;
    TypeSourceInfo *ParamTInfo =
        Context.getTrivialTypeSourceInfo(ParamType, RD->getEndLoc());
    ParmVarDecl *PVD = ParmVarDecl::Create(
        getASTContext(), Destructor, RD->getEndLoc(), RD->getEndLoc(),
        &(getASTContext().Idents).get("this"), ParamType, ParamTInfo, SC_None,
        nullptr);
    ProtoLoc.setParam(0, PVD);

    ParmVarDecls.push_back(PVD);
    Destructor->setParams(ParmVarDecls);
    RD->addDecl(Destructor);
    Destructor->setLexicalDeclContext(getASTContext().getTranslationUnitDecl());
    Destructor->setDestructor(true);
    CompoundStmt *CS =
        CompoundStmt::Create(getASTContext(), {}, FPOptionsOverride(),
                             RD->getEndLoc(), RD->getEndLoc());
    Destructor->setBody(CS);
    PushOnScopeChains(Destructor, getCurScope(), false);
  } else {
    Destructor = RD->getBSCDestructor();
  }
  return Destructor;
}

// Collect all owned struct type fields that has destructor,
// including nested owned struct type fields.
static void CollectAllFieldsWithPendingInstantiatedDestructor(RecordDecl *RD,
                                                              std::stack<RecordDecl *> &OwnedStructFields) {
  for (RecordDecl::field_iterator FieldIt = RD->field_begin();
       FieldIt != RD->field_end(); ++FieldIt) {
    const Type *FieldType = FieldIt->getType().getCanonicalType().getTypePtr();
    if (FieldType->isOwnedStructureType()) {
      RecordDecl *RD = cast<RecordType>(FieldType)->getDecl();
      if (RD->getBSCDestructor() && !RD->getBSCDestructor()->isInvalidDecl()) {
        OwnedStructFields.push(RD);
        CollectAllFieldsWithPendingInstantiatedDestructor(RD, OwnedStructFields);
      }
    }
  }
}

void Sema::HandleBSCDestructorBody(RecordDecl *RD, BSCMethodDecl *Destructor,
                                   std::stack<FieldDecl *> InstanceFields) {
  if (InstanceFields.empty())
    return;
  Stmt *FuncBody = Destructor->getBody();
  if (FuncBody) {
    if (auto *CS = dyn_cast<CompoundStmt>(FuncBody)) {
      std::vector<Stmt *> Stmts;
      for (auto *C : CS->children()) {
        Stmts.push_back(C);
      }
      while (!InstanceFields.empty()) {
        FieldDecl *Field = InstanceFields.top();
        InstanceFields.pop();

        const Type *FieldType = Field->getType().getCanonicalType().getTypePtr();
        if (FieldType->isOwnedStructureType()) {
          RecordDecl *ThisRD = cast<RecordType>(FieldType)->getDecl();
          BSCMethodDecl *DestructorToCall = ThisRD->getBSCDestructor();
          ParmVarDecl *PVD = Destructor->getParamDecl(0);
          QualType ParamType = getASTContext().getRecordType(RD);
          ParamType.addOwned();

          Expr *DRE =
              BuildDeclRefExpr(PVD, ParamType, VK_LValue, CS->getRBracLoc());
          if (!ParamType->getAsCXXRecordDecl()) {
            DRE = ImplicitCastExpr::Create(Context, ParamType, CK_LValueToRValue,
                                          DRE, nullptr, VK_PRValue,
                                          FPOptionsOverride());
          }
          Expr *MemberExpr = BuildMemberExpr(
              DRE, false, SourceLocation(), NestedNameSpecifierLoc(),
              SourceLocation(), Field,
              DeclAccessPair::make(RD, Field->getAccess()), false,
              DeclarationNameInfo(), Field->getType().getNonReferenceType(),
              VK_LValue, OK_Ordinary);
          SmallVector<Expr *, 1> Args;
          Args.push_back(MemberExpr);
          Expr *DestructorRef =
              BuildDeclRefExpr(DestructorToCall, DestructorToCall->getType(),
                              VK_LValue, SourceLocation());
          DestructorRef =
              ImpCastExprToType(DestructorRef,
                                Context.getPointerType(DestructorRef->getType()),
                                CK_FunctionToPointerDecay)
                  .get();
          Expr *CE = BuildCallExpr(nullptr, DestructorRef, SourceLocation(), Args,
                                  SourceLocation())
                        .get();
          Stmts.push_back(CE);

          // If a owned struct has nested owned structs which should be instantiated,
          // we add destructors of all nested owned structs to PendingInstantiations,
          // the functions in which will be instantiated in ActOnEndOfTranslationUnit().
          // For example:
          // @code
          //     owned struct A<T> {};
          //     owned struct B<T> { A<T> a; };
          //     owned struct C { B<int> b; };
          // @endcode
          // When desugar destructor of C, above we have added destructor of B<int> to PendingInstantiations,
          // here we add destructor of A<int> to PendingInstantiations.
          std::stack<RecordDecl *> OwnedStructFields;
          CollectAllFieldsWithPendingInstantiatedDestructor(ThisRD,
                                                            OwnedStructFields);
          while (!OwnedStructFields.empty()) {
            RecordDecl *RDOfOwnerStructField = OwnedStructFields.top();
            OwnedStructFields.pop();
            BSCMethodDecl *DestructorOfOwnerStructField =
                RDOfOwnerStructField->getBSCDestructor();
            SourceLocation PointOfInstantiation =
                DestructorOfOwnerStructField->getPointOfInstantiation();
            DestructorOfOwnerStructField->setInstantiationIsPending(true);
            PendingInstantiations.push_back(
                std::make_pair(DestructorOfOwnerStructField, PointOfInstantiation));
          }
        }
      }
      CompoundStmt *NewCS =
          CompoundStmt::Create(getASTContext(), Stmts, FPOptionsOverride(),
                              CS->getLBracLoc(), CS->getRBracLoc());
      Destructor->setBody(NewCS);
    }
  }
}

namespace {

class DeclRefFinder : public RecursiveASTVisitor<DeclRefFinder> {
  Sema &SemaRef;

public:
  DeclRefFinder(Sema &SemaRef) : SemaRef(SemaRef) {}

  bool VisitCallExpr(CallExpr *CE) {
    for (auto it = CE->arg_begin(), ei = CE->arg_end(); it != ei; ++it) {
      RecursiveASTVisitor<DeclRefFinder>::TraverseStmt(*it);
    }
    return false;
  }
  bool VisitDeclRefExpr(DeclRefExpr *E) {
    if (isa<VarDecl>(E->getDecl()) &&
        IsVarDeclWithOwnedStructureType(cast<VarDecl>(E->getDecl()))) {
      MovedDecls.push_back(cast<VarDecl>(E->getDecl()));
    }
    return true;
  }
  bool VisitBinaryOperator(const BinaryOperator *BOp) {
    if (isa<DeclRefExpr>(BOp->getLHS())) {
      auto E = cast<DeclRefExpr>(BOp->getLHS());
      if (isa<VarDecl>(E->getDecl()) &&
          IsVarDeclWithOwnedStructureType(cast<VarDecl>(E->getDecl()))) {
        ReAssignedDecls.push_back(cast<VarDecl>(E->getDecl()));
      }
    }
    if (BOp->getRHS()) {
      RecursiveASTVisitor<DeclRefFinder>::TraverseStmt(BOp->getRHS());
    }
    return false;
  }

  bool VisitUnaryOperator(const UnaryOperator *UOp) { return false; }

  bool VisitMemberExpr(const MemberExpr *MA) { return false; }

  llvm::SmallVector<VarDecl *> MovedDecls;
  llvm::SmallVector<VarDecl *> ReAssignedDecls;
};
llvm::DenseMap<CompoundStmt *, CompoundStmt *> ReplaceCompoundMap;

class InsertDestructorCallStmt
    : public RecursiveASTVisitor<InsertDestructorCallStmt> {
  Sema &SemaRef;
  std::vector<CompoundStmt *> CompoundStmts;
  llvm::DenseMap<VarDecl *, VarDecl *> FlagMap;
  FunctionDecl *FD;

public:
  explicit InsertDestructorCallStmt(Sema &SemaRef) : SemaRef(SemaRef) {}

  Stmt *AddIfStmt(VarDecl *VD) {
    assert(IsVarDeclWithOwnedStructureType(VD));
    const Type *VDType = VD->getType().getCanonicalType().getTypePtr();
    RecordDecl *RD = cast<RecordType>(VDType)->getDecl();
    BSCMethodDecl *DestructorToCall = SemaRef.getOrInsertBSCDestructor(RD);
    Expr *IDRE = SemaRef.BuildDeclRefExpr(VD, VD->getType().getCanonicalType(),
                                          VK_LValue, SourceLocation());
    SmallVector<Expr *, 1> Args;
    Args.push_back(IDRE);
    Expr *DestructorRef =
        SemaRef.BuildDeclRefExpr(DestructorToCall, DestructorToCall->getType(),
                                 VK_LValue, SourceLocation());
    DestructorRef = SemaRef
                        .ImpCastExprToType(DestructorRef,
                                           SemaRef.Context.getPointerType(
                                               DestructorRef->getType()),
                                           CK_FunctionToPointerDecay)
                        .get();
    Expr *CE = SemaRef
                   .BuildCallExpr(nullptr, DestructorRef, SourceLocation(),
                                  Args, SourceLocation())
                   .get();
    if (!CE) {
      return nullptr;
    }
    Expr *FlagRefExpr = SemaRef.BuildDeclRefExpr(
        FlagMap[VD], FlagMap[VD]->getType(), VK_LValue, SourceLocation());
    FlagRefExpr =
        SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_LNot, FlagRefExpr)
            .get();
    Sema::ConditionResult IfCond = SemaRef.ActOnCondition(
        nullptr, SourceLocation(), FlagRefExpr, Sema::ConditionKind::Boolean);
    Stmt *If = SemaRef
                   .BuildIfStmt(
                       SourceLocation(), IfStatementKind::Ordinary,
                       /*LPL=*/SourceLocation(), /*Init=*/nullptr, IfCond,
                       /*RPL=*/SourceLocation(), CE, SourceLocation(), nullptr)
                   .get();
    return If;
  }

  // Add if stmt for owned struct type vardecl.
  std::vector<Stmt *> AddIfStmts(Stmt *S) {
    std::vector<Stmt *> IfStmts;
    SmallVector<VarDecl *> VarDecls = SemaRef.Context.DestructMap[FD][S];
    for (auto *VD : VarDecls) {
      Stmt *If = AddIfStmt(VD);
      IfStmts.push_back(If);
    }
    return IfStmts;
  }
  // Create _Bool xx_is_moved = 0;
  DeclStmt *CreateMoveFlag(VarDecl *D) {
    std::string IName = D->getName().str() + "_is_moved";
    VarDecl *VD =
        VarDecl::Create(SemaRef.Context, FD, D->getLocation(), D->getLocation(),
                        &(SemaRef.Context.Idents).get(IName),
                        SemaRef.Context.BoolTy, nullptr, SC_None);
    llvm::APInt Zero(SemaRef.Context.getTypeSize(SemaRef.Context.IntTy), 0);
    Expr *IInit = IntegerLiteral::Create(
        SemaRef.Context, Zero, SemaRef.Context.IntTy, SourceLocation());
    IInit = SemaRef
                .ImpCastExprToType(IInit, SemaRef.Context.BoolTy,
                                   CK_IntegralToBoolean)
                .get();
    VD->setInit(IInit);
    DeclGroupRef DataDG(VD);
    DeclStmt *DataDS = new (SemaRef.Context)
        DeclStmt(DataDG, D->getLocation(), D->getLocation());
    FlagMap[D] = VD;
    return DataDS;
  }

  // Create xx_is_moved = 1;
  Stmt *MoveFlagStatusUpdate(VarDecl *D, uint64_t Value = 1) {
    Expr *LHS = SemaRef.BuildDeclRefExpr(FlagMap[D], FlagMap[D]->getType(),
                                         VK_LValue, SourceLocation());
    llvm::APInt One(SemaRef.Context.getTypeSize(SemaRef.Context.IntTy), Value);
    Expr *IInit = IntegerLiteral::Create(
        SemaRef.Context, One, SemaRef.Context.IntTy, SourceLocation());
    IInit = SemaRef
                .ImpCastExprToType(IInit, SemaRef.Context.BoolTy,
                                   CK_IntegralToBoolean)
                .get();
    Expr *BinOpExpr =
        SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, LHS, IInit)
            .get();
    return BinOpExpr;
  }

  bool VisitCompoundStmt(CompoundStmt *CS) {
    CompoundStmts.push_back(CS);
    std::vector<Stmt *> Statements;
    if (CS == FD->getBody()) {
      for (ParmVarDecl *PVD : FD->parameters()) {
        if (IsVarDeclWithOwnedStructureType(PVD)) {
          Statements.push_back(CreateMoveFlag(PVD));
        }
      }
    }
    bool HasControlTransferExpr = false;
    for (auto *C : CS->children()) {
      Stmt *S = const_cast<Stmt *>(C);
      // Add destructor call if-stmt for all defined vardecls before exit current block
      if (isa<ReturnStmt>(S) || isa<BreakStmt>(S) || isa<ContinueStmt>(S)) {
        HasControlTransferExpr = true;
        std::vector<Stmt *> IfStmts = AddIfStmts(S);
        Statements.insert(Statements.end(), IfStmts.begin(), IfStmts.end());
      }
      RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseStmt(C);
      if (isa<CompoundStmt>(S)) {
        Statements.push_back(ReplaceCompoundMap[dyn_cast<CompoundStmt>(S)]);
      } else if (isa<LabelStmt>(S)) {
        auto labelStmt = cast<LabelStmt>(S);
        if (!isa<CompoundStmt>(labelStmt->getSubStmt())) {
          auto stmts = CreateStatements(labelStmt->getSubStmt());
          labelStmt->setSubStmt(stmts[0]);
          Statements.push_back(labelStmt);
          Statements.insert(Statements.end(), stmts.begin() + 1, stmts.end());
        } else {
          Statements.push_back(C);
        }
      } else {
        // add destructor call if-stmt for reassigned decl in BinaryOperator
        if (isa<BinaryOperator>(S)) {
          DeclRefFinder Finder = DeclRefFinder(SemaRef);
          Finder.TraverseStmt(S);
          for (auto *D : Finder.ReAssignedDecls) {
            Stmt *IfStmt = AddIfStmt(D);
            Statements.push_back(IfStmt);
          }
        }
        Statements.push_back(C);
      }
      if (isa<DeclStmt>(S)) {
        // add _Bool xx_is_moved = 0;
        for (auto *D : cast<DeclStmt>(S)->decls()) {
          if (isa<VarDecl>(D)) {
            VarDecl *VD = cast<VarDecl>(D);
            if (IsVarDeclWithOwnedStructureType(VD)) {
              Statements.push_back(CreateMoveFlag(VD));
            }
          }
        }
      }

      if (isa<BinaryOperator>(S) || isa<DeclStmt>(S) || isa<CallExpr>(S)) {
        // change reassigned_decl_is_moved = 0, and moved_decl_is_moved = 1
        DeclRefFinder Finder = DeclRefFinder(SemaRef);
        Finder.TraverseStmt(S);
        for (auto *D : Finder.ReAssignedDecls) {
          Statements.push_back(MoveFlagStatusUpdate(D, 0));
        }
        for (auto *D : Finder.MovedDecls) {
          Statements.push_back(MoveFlagStatusUpdate(D));
        }
      }
    }
    if (!HasControlTransferExpr) {
      // If no return/break/continue stmts, create destructor call if-stmt for all defined vardecls before exit
      auto IfStmts = AddIfStmts(CS);
      Statements.insert(Statements.end(), IfStmts.begin(), IfStmts.end());
    }
    auto NewCPStmt = CompoundStmt::Create(SemaRef.getASTContext(), Statements,
                                          FPOptionsOverride(),
                                          CS->getLBracLoc(), CS->getRBracLoc(),
                                          CS->getSafeSpecifier(),
                                          CS->getSafeSpecifierLoc(),
                                          CS->getCompSafeZoneSpecifier());
    ReplaceCompoundMap[CS] = NewCPStmt;
    return false;
  }

  std::vector<Stmt *> CreateStatements(Stmt *S) {
    std::vector<Stmt *> Statements;
    if (isa<ReturnStmt>(S) || isa<BreakStmt>(S) || isa<ContinueStmt>(S)) {
      std::vector<Stmt *> IfStmts = AddIfStmts(S);
      Statements.insert(Statements.end(), IfStmts.begin(), IfStmts.end());
    }
    Statements.push_back(S);
    if (isa<DeclStmt>(S)) {
      for (auto *D : cast<DeclStmt>(S)->decls()) {
        if (isa<VarDecl>(D)) {
          VarDecl *VD = cast<VarDecl>(D);
          if (IsVarDeclWithOwnedStructureType(VD)) {
            Statements.push_back(CreateMoveFlag(VD));
            Statements.push_back(AddIfStmt(VD));
          }
        }
      }
    }
    if (isa<BinaryOperator>(S) || isa<DeclStmt>(S) || isa<CallExpr>(S)) {
      DeclRefFinder Finder = DeclRefFinder(SemaRef);
      Finder.TraverseStmt(S);
      for (auto *D : Finder.ReAssignedDecls) {
        Statements.push_back(MoveFlagStatusUpdate(D, 0));
      }
      for (auto *D : Finder.MovedDecls) {
        Statements.push_back(MoveFlagStatusUpdate(D));
      }
    }
    return Statements;
  }

  Stmt *CreateNewCompoundStmt(Stmt *S) {
    auto Stmts = CreateStatements(S);
    if (Stmts.size() <= 1)
      return S;
    return CompoundStmt::Create(SemaRef.getASTContext(), Stmts,
                                FPOptionsOverride(), SourceLocation(),
                                SourceLocation());
  }

  bool TraverseWhileStmt(WhileStmt *WS) {
    if (WS->getBody()) {
      RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseStmt(WS->getBody());
      if (auto NewCompound =
              ReplaceCompoundMap[dyn_cast<CompoundStmt>(WS->getBody())]) {
        WS->setBody(NewCompound);
      } else {
        WS->setBody(CreateNewCompoundStmt(WS->getBody()));
      }
    }
    return false;
  }

  bool TraverseIfStmt(IfStmt *IS) {
    if (IS->getThen()) {
      RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseStmt(
          IS->getThen());
      if (auto NewCompound = dyn_cast<CompoundStmt>(IS->getThen())) {
        IS->setThen(ReplaceCompoundMap[NewCompound]);
      } else {
        IS->setThen(CreateNewCompoundStmt(IS->getThen()));
      }
    }
    if (IS->getElse()) {
      RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseStmt(
          IS->getElse());
      if (auto NewCompound = dyn_cast<CompoundStmt>(IS->getElse())) {
        IS->setElse(ReplaceCompoundMap[NewCompound]);
      } else {
        IS->setElse(CreateNewCompoundStmt(IS->getElse()));
      }
    }
    return false;
  }

  bool TraverseDoStmt(DoStmt *DS) {
    if (DS->getBody()) {
      RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseStmt(DS->getBody());
      if (auto NewCompound = dyn_cast<CompoundStmt>(DS->getBody())) {
        DS->setBody(ReplaceCompoundMap[NewCompound]);
      } else {
        DS->setBody(CreateNewCompoundStmt(DS->getBody()));
      }
    }
    return false;
  }
  bool TraverseForStmt(ForStmt *FS) {
    if (FS->getBody()) {
      RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseStmt(FS->getBody());
      if (auto NewCompound = dyn_cast<CompoundStmt>(FS->getBody())) {
        FS->setBody(ReplaceCompoundMap[NewCompound]);
      } else {
        FS->setBody(CreateNewCompoundStmt(FS->getBody()));
      }
    }
    return false;
  }

  bool TraverseLabelStmt(LabelStmt *LS) {
    RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseLabelStmt(LS);
    if (auto NewCompound = dyn_cast<CompoundStmt>(LS->getSubStmt())) {
      LS->setSubStmt(ReplaceCompoundMap[NewCompound]);
    }
    return false;
  }

  bool TraverseSwitchStmt(SwitchStmt *SS) {
    if (SS->getBody()) {
      RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseStmt(SS->getBody());
      if (auto NewCompound = dyn_cast<CompoundStmt>(SS->getBody())) {
        SS->setBody(ReplaceCompoundMap[NewCompound]);
      }
    }
    return false;
  }

  bool TraverseDefaultStmt(DefaultStmt *DS) {
    RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseDefaultStmt(DS);
    if (auto NewCompound = dyn_cast<CompoundStmt>(DS->getSubStmt())) {
      DS->setSubStmt(ReplaceCompoundMap[NewCompound]);
    }
    return false;
  }

  bool TraverseCaseStmt(CaseStmt *CS) {
    RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseCaseStmt(CS);
    if (auto NewCompound = dyn_cast<CompoundStmt>(CS->getSubStmt())) {
      CS->setSubStmt(ReplaceCompoundMap[NewCompound]);
    }
    return false;
  }

  bool TraverseFunctionDecl(FunctionDecl *D) {
    FD = D;
    RecursiveASTVisitor<InsertDestructorCallStmt>::TraverseFunctionDecl(D);
    if (D->getBody() != nullptr) {
      if (auto NewCompound =
              ReplaceCompoundMap[dyn_cast<CompoundStmt>(D->getBody())]) {
        D->setBody(NewCompound);
      }
    }
    return false;
  }
};

} // namespace

class CalcDestructorMapForIns
    : public RecursiveASTVisitor<CalcDestructorMapForIns> {
  Sema &SemaRef;
  FunctionDecl *FD;
  bool IsDestructor = false;
  std::stack<CompoundStmt *> VisitCompoundStmtStack;
  llvm::DenseMap<CompoundStmt *, SmallVector<VarDecl *>> CS2Vars;
  std::stack<CompoundStmt *> VisitLoopCompoundStmtStack;

public:
  explicit CalcDestructorMapForIns(Sema &SemaRef) : SemaRef(SemaRef) {}

  bool VisitReturnStmt(ReturnStmt *RS) {
    if (!VisitCompoundStmtStack.empty()) {
      DeclRefFinder Finder = DeclRefFinder(SemaRef);
      Finder.TraverseStmt(RS);
      SmallVector<VarDecl *> MovedDecls = Finder.MovedDecls;
      std::stack<CompoundStmt *> tempStack = VisitCompoundStmtStack;
      SmallVector<VarDecl *> newVarDecls;
      while (!tempStack.empty()) {
        auto CompoundStmt = tempStack.top();
        for (auto iter = CS2Vars[CompoundStmt].begin();
             iter != CS2Vars[CompoundStmt].end(); iter++) {
          VarDecl *D = *iter;
          if (std::find(MovedDecls.begin(), MovedDecls.end(), D) ==
              MovedDecls.end()) {
            newVarDecls.insert(newVarDecls.end(), D);
          }
        }
        tempStack.pop();
      }
      if (newVarDecls.size() != 0) {
        SemaRef.Context.DestructMap[FD][RS] = newVarDecls;
      }
    }
    return false;
  }

  void CalcDestructMapForBreakAndContinue(Stmt *S) {
    if (!VisitLoopCompoundStmtStack.empty()) {
      std::stack<CompoundStmt *> tempStack = VisitCompoundStmtStack;
      SmallVector<VarDecl *> newVarDecls;
      while (!tempStack.empty() &&
             tempStack.top() != VisitLoopCompoundStmtStack.top()) {
        auto CompoundStmt = tempStack.top();
        newVarDecls.insert(newVarDecls.begin(), CS2Vars[CompoundStmt].begin(),
                           CS2Vars[CompoundStmt].end());
        tempStack.pop();
      }
      if (!tempStack.empty() &&
          tempStack.top() == VisitLoopCompoundStmtStack.top()) {
        auto CompoundStmt = tempStack.top();
        newVarDecls.insert(newVarDecls.begin(), CS2Vars[CompoundStmt].begin(),
                           CS2Vars[CompoundStmt].end());
        tempStack.pop();
      }
      if (newVarDecls.size() != 0) {
        SemaRef.Context.DestructMap[FD][S] = newVarDecls;
      }
    }
  }

  bool VisitBreakStmt(BreakStmt *BS) {
    CalcDestructMapForBreakAndContinue(BS);
    return false;
  }
  bool VisitContinueStmt(ContinueStmt *CS) {
    CalcDestructMapForBreakAndContinue(CS);
    return false;
  }

  bool TraverseCompoundStmt(CompoundStmt *CS) {
    VisitCompoundStmtStack.push(CS);
    SmallVector<VarDecl *> &VarDecls = CS2Vars[CS];
    if (CS == FD->getBody() && !IsDestructor) {
      for (ParmVarDecl *PVD : FD->parameters()) {
        if (IsVarDeclWithOwnedStructureType(PVD)) {
          VarDecls.insert(VarDecls.begin(), PVD);
        }
      }
    }

    for (auto *C : CS->children()) {
      Stmt *S = const_cast<Stmt *>(C);
      if (DeclStmt *StmtDecl = dyn_cast<DeclStmt>(S)) {
        for (auto *SD : StmtDecl->decls()) {
          if (auto VD = dyn_cast<VarDecl>(SD)) {
            bool InTopLevelSwitchBlock = VD->isDefInTopLevelSwitchBlock();
            if (IsVarDeclWithOwnedStructureType(VD) && !InTopLevelSwitchBlock) {
              VarDecls.insert(VarDecls.begin(), VD);
            }
          }
        }
      }
      RecursiveASTVisitor<CalcDestructorMapForIns>::TraverseStmt(C);
    }
    if (VarDecls.size() != 0) {
      SemaRef.Context.DestructMap[FD][CS] = VarDecls;
    }
    VisitCompoundStmtStack.pop();
    return true;
  }

  bool TraverseSwitchStmt(SwitchStmt *SS) {
    if (isa<CompoundStmt>(SS->getBody())) {
      VisitLoopCompoundStmtStack.push(dyn_cast<CompoundStmt>(SS->getBody()));
    }
    RecursiveASTVisitor<CalcDestructorMapForIns>::TraverseSwitchStmt(SS);

    if (isa<CompoundStmt>(SS->getBody())) {
      VisitLoopCompoundStmtStack.pop();
    }
    return false;
  }

  bool TraverseWhileStmt(WhileStmt *WS) {
    if (isa<CompoundStmt>(WS->getBody())) {
      VisitLoopCompoundStmtStack.push(dyn_cast<CompoundStmt>(WS->getBody()));
    }
    RecursiveASTVisitor<CalcDestructorMapForIns>::TraverseWhileStmt(WS);

    if (isa<CompoundStmt>(WS->getBody())) {
      VisitLoopCompoundStmtStack.pop();
    }
    return false;
  }

  bool TraverseDoStmt(DoStmt *DS) {
    if (isa<CompoundStmt>(DS->getBody())) {
      VisitLoopCompoundStmtStack.push(dyn_cast<CompoundStmt>(DS->getBody()));
    }
    RecursiveASTVisitor<CalcDestructorMapForIns>::TraverseDoStmt(DS);

    if (isa<CompoundStmt>(DS->getBody())) {
      VisitLoopCompoundStmtStack.pop();
    }
    return false;
  }
  bool TraverseForStmt(ForStmt *FS) {
    if (isa<CompoundStmt>(FS->getBody())) {
      VisitLoopCompoundStmtStack.push(dyn_cast<CompoundStmt>(FS->getBody()));
    }

    RecursiveASTVisitor<CalcDestructorMapForIns>::TraverseForStmt(FS);
    if (isa<CompoundStmt>(FS->getBody())) {
      VisitLoopCompoundStmtStack.pop();
    }
    return false;
  }
  bool TraverseFunctionDecl(FunctionDecl *D) {
    FD = D;
    if (auto MD = dyn_cast<BSCMethodDecl>(D)) {
      IsDestructor = MD->isDestructor();
    }
    return RecursiveASTVisitor<CalcDestructorMapForIns>::TraverseFunctionDecl(
        D);
  }
};

void Sema::DesugarDestructorCall(FunctionDecl *FD) {
  if (!getLangOpts().BSC)
    return;
  // Skip function template and class template.
  if (auto RD = dyn_cast<RecordDecl>(FD->getParent())) {
    if (RD->getDescribedClassTemplate() != nullptr)
      return;
  }
  if (FD->getTemplatedKind() == FunctionDecl::TK_FunctionTemplate)
    return;
  CollDestructMapInFuncInstantiation(FD);
  // Insert destructor function calls.
  InsertDestructorCallStmt IDCS(*this);
  IDCS.TraverseFunctionDecl(FD);
}

void Sema::DesugarDestructor(RecordDecl *RD) {
  if (!getLangOpts().BSC || !RD->isOwnedDecl() || !RD->isCompleteDefinition()) {
    return;
  }
  BSCMethodDecl *Destructor = getOrInsertBSCDestructor(RD);
  if (Destructor->isInvalidDecl())
    return;
  std::stack<FieldDecl *> Fields = CollectInstanceFieldWithDestructor(RD);
  HandleBSCDestructorBody(RD, Destructor, Fields);
  BSCDataflowAnalysis(Destructor);
}

void Sema::CheckBSCDestructorDeclarator(FunctionDecl *NewFD) {
  RecordDecl *Record = cast<RecordDecl>(NewFD->getParent());
  if (Record->isInvalidDecl())
    return;
  QualType ClassType = Context.getTypeDeclType(Record);
  DeclarationName Name = Context.DeclarationNames.getCXXDestructorName(
      Context.getCanonicalType(ClassType));
  if (NewFD->getDeclName() != Name) {
    Diag(NewFD->getLocation(), diag::err_owned_struct_destructor_name);
    NewFD->setInvalidDecl();
    return;
  }

  std::string TypeName;
  if (isa<InjectedClassNameType>(ClassType)) {
    // handle generic owned struct type
    TypeName = ClassType.getAsString();
  } else {
    TypeName = ClassType.getBaseTypeIdentifier()->getName().str();
  }

  if (NewFD->getNumParams() == 0) {
    Diag(NewFD->getLocation(), diag::invalid_param_for_destructor) << TypeName;
    NewFD->setInvalidDecl();
    return;
  }

  bool IsEqualType = true;
  if (isa<InjectedClassNameType>(ClassType)) {
    IsEqualType = ("owned " + ClassType.getAsString()) ==
                  NewFD->getParamDecl(0)->getType().getAsString();
  } else {
    auto ParamType = NewFD->getParamDecl(0)->getType().getTypePtrOrNull();
    if (auto CT = ClassType.getTypePtrOrNull()) {
      IsEqualType = CT->getCanonicalTypeUnqualified().getTypePtrOrNull() ==
                    ParamType->getCanonicalTypeUnqualified().getTypePtrOrNull();
    }
  }

  if ((!IsEqualType || NewFD->getParamDecl(0)->getName() != "this")) {
    Diag(NewFD->getParamDecl(0)->getLocation(),
         diag::invalid_param_for_destructor)
        << TypeName;
    NewFD->setInvalidDecl();
    return;
  }

  if (NewFD->getNumParams() > 1) {
    Diag(NewFD->getLocation(), diag::invalid_param_num_for_destructor);
    NewFD->setInvalidDecl();
    return;
  }
}

void Sema::CheckBSCDestructorBody(FunctionDecl *NewFD) {
  if (NewFD->getBody() == nullptr) {
    Diag(NewFD->getLocation(), diag::err_owned_struct_destructor_body);
    NewFD->setInvalidDecl();
  }
}

// Collect the destructor map of non-instantiated functions.
void Sema::CollectDestructMap(StmtResult Res, Scope *BeginScope,
                              Scope *EndScope) {
  if (!getLangOpts().BSC || Res.isInvalid() || !Res.get())
    return;
  llvm::SmallVector<VarDecl *> MovedDecls;
  if (isa<ReturnStmt>(Res.get())) {
    ReturnStmt *Value = cast<ReturnStmt>(Res.get());
    // should find var
    DeclRefFinder Finder = DeclRefFinder(*this);
    Finder.TraverseStmt(Value);
    MovedDecls = Finder.MovedDecls;
  }
  SmallVector<VarDecl *> ReturnStmts;
  while (BeginScope != EndScope->getParent()) {
    std::stack<VarDecl *> VarDeclStack =
        BeginScope->DeclsInScopeToEmitDestructorCall;
    while (!VarDeclStack.empty()) {
      VarDecl *D = VarDeclStack.top();
      bool IsTopLevelSwitchBlock =
          BeginScope->getParent()->getFlags() & Scope::SwitchScope;
      VarDeclStack.pop();
      bool IsDestructorParam = false;
      if (auto MD = dyn_cast<BSCMethodDecl>(getCurFunctionOrMethodDecl())) {
        IsDestructorParam = MD->isDestructor() && isa<ParmVarDecl>(D);
      }
      if ((std::find(MovedDecls.begin(), MovedDecls.end(), D) ==
           MovedDecls.end()) &&
          !IsTopLevelSwitchBlock && !IsDestructorParam) {
        ReturnStmts.push_back(D);
      }
    }
    BeginScope = BeginScope->getParent();
  }

  if (ReturnStmts.size() != 0) {
    Context.DestructMap[getCurFunctionOrMethodDecl()][Res.get()] = ReturnStmts;
  }
}

// Collect destructor map during function instantiation,the destructor map of
// non-instantiated functions has already been collected in the parser phase.
void Sema::CollDestructMapInFuncInstantiation(FunctionDecl *FD) {
  if (FD->getTemplatedKind() == FunctionDecl::TK_NonTemplate)
    return;
  CalcDestructorMapForIns CalcDestructorMapForInsObj(*this);
  CalcDestructorMapForInsObj.TraverseFunctionDecl(FD);
}

#endif