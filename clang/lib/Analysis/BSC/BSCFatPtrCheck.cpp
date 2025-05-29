#if ENABLE_BSC

#include "clang/Analysis/Analyses/BSC/BSCFatPtrCheck.h"
#include "clang/AST/ParentMap.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CFG.h"
#include "clang/Analysis/FlowSensitive/DataflowWorklist.h"
#include "llvm/ADT/DenseMap.h"

using namespace clang;

/// Represents the check status of a fat pointer's associated VarDecl after the last operation that may modify it, 
/// such as free(p) or p++.
enum class FatPtrCheckStatus : uint8_t {
  Unchecked = 0,       // No checks have been performed

  KeyCheckedOnly = 1,  // Only the key was checked

  OffsetCheckedOnly = 2, // Only the offset was checked

  BothChecked = 3,      // Both the key and the offset were checked
};

using FatPtrVar = std::pair<VarDecl *, std::string>;
using FatPtrVarCheckStatus = std::map<FatPtrVar, FatPtrCheckStatus>;

class FatPtrCheckImpl {
public:
  // record each BB's Last and Out pointer var check status
  llvm::DenseMap<const CFGBlock *, FatPtrVarCheckStatus> BBLastStatus;
  llvm::DenseMap<const CFGBlock *, FatPtrVarCheckStatus> BBOutStatus;

  // For branch statement with condition, such as IfStmt, WhileStmt,
  // true branch and else branch may have different status.
  // we merge the check status of all the paths to the current BB
  // For example:
  // @code
  //     int *fat p = checked_malloc(sizeof(int));
  //     *p = 0;
  //     if (p != nullptr) {
  //         use(p); // p is perhaps freed
  //     } else {
  //         *p = 10;  // p is checked before, so the check of p can be deleted here
  //     }
  //     *p = 5;   // p may be freed after the ifstmt, so the check of p is kept here
  // @endcode
  // CFG is:
  //        B4(has condition as terminitor)
  //    true /      \ false
  //        B3      B2
  //          \    /
  //            B1
  // BBOutStatus records the check status of each BB:
  // Key is current BB, value is the status after all the statements in current
  // for this example, BBOutStatus will be:
  // { B4 : p BothChecked }, { B3 : p Unchecked }, { B2 : p BothChecked }, { B1 : p BothChecked }
  // Before caculating BBOutStatus of each BB, we merge the check status of all the pred BBs,
  // And then, use the merged status as the input of the current BB.
  // for B1, the input check status of p is: BBOutStatus[B3][p] & BBOutStatus[B2][p]

  // BBLastStatus records the check status of each BB at last analysis:
  // After analysis of current BB, we compare the BBOutStatus and BBLastStatus, 
  // if they are different, we add the subsequent BB of the current BB to the analysis worklist.

  FatPtrVarCheckStatus runOnBlock(const CFGBlock *block,
                                  FatPtrVarCheckStatus &status, ASTContext &ctx,
                                  const FunctionDecl &fd, ParentMap &PM);

  void initStatus(const CFG &cfg, ASTContext &ctx);
  FatPtrVarCheckStatus mergePredStatus(FatPtrVarCheckStatus currStatus,
                                       FatPtrVarCheckStatus predStatus);

  FatPtrCheckImpl() : BBLastStatus(0), BBOutStatus(0) {}
};

namespace {
class TransferFunctions : public StmtVisitor<TransferFunctions> {
  FatPtrCheckImpl &FCI;
  const CFGBlock *Block;
  FatPtrVarCheckStatus &CurrStatus;
  ASTContext &Ctx;
  const FunctionDecl &Fd;
  ParentMap &PM;
  CallGraph CG;

public:
  TransferFunctions(FatPtrCheckImpl &fci, const CFGBlock *block,
                    FatPtrVarCheckStatus &status, ASTContext &ctx,
                    const FunctionDecl &fd, ParentMap &pm)
      : FCI(fci), Block(block), CurrStatus(status), Ctx(ctx), Fd(fd), PM(pm){}
  
  bool mayFreeCallExpr(CallExpr *CE);
  void VisitBinaryOperator(BinaryOperator *BO);
  void VisitUnaryOperator(UnaryOperator *UO);
  void VisitMemberExpr(MemberExpr *ME);
  void VisitCallExpr(CallExpr *CE);
  void VisitCStyleCastExpr(CStyleCastExpr *CSCE);
  void VisitArraySubscriptExpr(ArraySubscriptExpr *ASE);

private:
  // The whitelist of functions that will not free heap memory.
  // FIXME: Add more common libc functions that do not free.
  std::set<std::string> MayFreeFnWL = {
    "malloc", "checked_malloc", "_check_version", "_check_offset", "_check_version_and_offset", "_new_version_number",
    // libc C functions. Need add more.
    "printf", "sprintf", "abort", "exit", "srand",
    "atoi", "atol",
    "strlen", "strcmp", "strncmp", "strcpy", "strncpy", "strcat", "strchar",
    "strtod", "strrchr", "strcasecmp", "strdup", "strstr", "strchr", "strpbrk",
    "strspn", "atoll",
    "memcpy", "memmove", "memcmp", "memset",
    "fread", "fputs", "fopen", "syslog", "opendir",
    "getpwnam", "getnameinfo",
    // Syscalls
    "stat", "readlink", "execve", "read", "write",
  };

};
} // namespace

static void VisitMEForFieldPath(Expr *E, FatPtrVar &FP) {
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

static DeclRefExpr *getDREFromExpr(Expr *E) {
  if (auto DRE = dyn_cast<DeclRefExpr>(E)) {
      return DRE;
  } else if (auto ICE = dyn_cast<ImplicitCastExpr>(E)) {
    return getDREFromExpr(ICE->getSubExpr());
  } else if (auto PE = dyn_cast<ParenExpr>(E)) {
    return getDREFromExpr(PE->getSubExpr());
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

static bool IsFatPtrSelfOffSetExpr(BinaryOperator *BO) {
  if (!BO->isAssignmentOp())
    return false;

  Expr *LHS = BO->getLHS();
  Expr *RHS = BO->getRHS();
  if (!LHS->getType().isFatPtrType())
    return false;

  // handle `p += 1`, `p -= 1`, if p is fat ptr.
  BinaryOperator::Opcode Op = BO->getOpcode();
  if ((Op == BO_AddAssign || Op == BO_SubAssign) &&
      RHS->getType()->isIntegerType())
    return true;
  
  // handle `p = p + 1`, if p is fat ptr.
  // eg. `p = p + 1`: true
  // eg. `p = p2 +1`: false
  if (auto *RHSBO = dyn_cast<BinaryOperator>(RHS)) {
    if (!RHSBO->isAdditiveOp())
      return false;
    
    Expr *RBLHS = RHSBO->getLHS();
    Expr *RBRHS = RHSBO->getRHS();
    if (!RBLHS->getType().isFatPtrType() || !RBRHS->getType()->isIntegerType())
      return false;
    
    if (auto *LHSDRF = getDREFromExpr(LHS)) {
      if (auto *RHSLeftDRE = getDREFromExpr(RBLHS)) {
        return LHSDRF->getDecl() == RHSLeftDRE->getDecl();
      }
    }
    // handle `p.a = p.a + 1`, if p.a is fat ptr.
    if (auto *LHSME = getMemberExprFromExpr(LHS)) {
      if (auto *RHSLeftME = getMemberExprFromExpr(RBLHS)) {
        return LHSME->getMemberDecl() == RHSLeftME->getMemberDecl();
      }
    }
  }
  return false;
}

void TransferFunctions::VisitBinaryOperator(BinaryOperator *BO) {
  Expr *LHS = BO->getLHS();
  if (!BO->isAssignmentOp() || !LHS->getType().isFatPtrType()) {
    return;
  }

  if (DeclRefExpr *DRE = getDREFromExpr(LHS)) {
    if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
      FatPtrVar FP = {VD, ""};
      if (!VD->getType().isFatPtrType() || !CurrStatus.count(FP)) {
        return;
      }
      if (IsFatPtrSelfOffSetExpr(BO)) {
        // handle `p = p + 1`, `p += 1`, if p is fat ptr.
        // reset the offset check status when p is self-offset
        CurrStatus[FP] = static_cast<FatPtrCheckStatus>(
            static_cast<uint8_t>(CurrStatus[FP]) &
            static_cast<uint8_t>(FatPtrCheckStatus::KeyCheckedOnly));
      } else {
        // reset the both check status when p is reassign
        // eg. `p = p2`, `p = p2 + 1`, `p = func()`
        CurrStatus[FP] = FatPtrCheckStatus::Unchecked;
      }
    }
  } else if (MemberExpr *ME = getMemberExprFromExpr(LHS)) {
    if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
      if (!FD->getType().isFatPtrType())
        return;
      FatPtrVar FP;
      VisitMEForFieldPath(ME, FP);
      if (!CurrStatus.count(FP))
        return;
      if (IsFatPtrSelfOffSetExpr(BO)) {
        // handle `p.a = p.a + 1`, `p.a += 1`, if p.a is fat ptr.
        // reset the offset check status when p is self-offset
        CurrStatus[FP] = static_cast<FatPtrCheckStatus>(
            static_cast<uint8_t>(CurrStatus[FP]) &
            static_cast<uint8_t>(FatPtrCheckStatus::KeyCheckedOnly));
      } else {
        // reset the both check status when p.a is reassign
        // eg. `p.a = p2.a`, `p.a = p2.a + 1`, `p.a = func()`
        CurrStatus[FP] = FatPtrCheckStatus::Unchecked;
      }
    }
  }
}

// *p will change the check status to BothChecked.
void TransferFunctions::VisitUnaryOperator(UnaryOperator *UO) {
  UnaryOperator::Opcode Op = UO->getOpcode();
  FatPtrVar FP;
  if (Op == UO_Deref || Op == UO_AddrMutDeref || Op == UO_AddrConstDeref) {
    // handle *p if p is fat ptr.
    if (DeclRefExpr *DRE = getDREFromExpr(UO->getSubExpr())) {
      if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
        FP = {VD, ""};
        if (VD->getType().isFatPtrType() && CurrStatus.count(FP)) {
          // Label the check kind in the sema phase, for unary expression: *p;
          Ctx.FatPtrCheckStatusMap[DRE] = static_cast<uint8_t>(CurrStatus[FP]);
          // update the redundant check status
          CurrStatus[FP] = FatPtrCheckStatus::BothChecked;
        }
      }
    } else if (MemberExpr *ME = getMemberExprFromExpr(UO->getSubExpr())) {
      // handle *(p->a), if p->a is fat ptr.
      if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
        if (FD->getType().isFatPtrType()) {
          VisitMEForFieldPath(ME, FP);
          if (CurrStatus.count(FP)) {
            Ctx.FatPtrCheckStatusMap[ME] = static_cast<uint8_t>(CurrStatus[FP]);
            CurrStatus[FP] = FatPtrCheckStatus::BothChecked;
          }
        }
      }
    }
  } else if (UO->isIncrementDecrementOp()) {
    // handle p++/p--/++p/--p if p is fat ptr.
    if (DeclRefExpr *DRE = getDREFromExpr(UO->getSubExpr())) {
      if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
        FP = {VD, ""};
        if (VD->getType().isFatPtrType() && CurrStatus.count(FP)) {
          // reset the offset check status when p is self-offset
          CurrStatus[FP] = static_cast<FatPtrCheckStatus>(
              static_cast<uint8_t>(CurrStatus[FP]) &
              static_cast<uint8_t>(FatPtrCheckStatus::KeyCheckedOnly));
        }
      }
    } else if (MemberExpr *ME = getMemberExprFromExpr(UO->getSubExpr())) {
      // handle (p->a)++, if p->a is fat ptr.
      if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
        if (FD->getType().isFatPtrType()) {
          // reset the offset check status when p is self-offset
          VisitMEForFieldPath(ME, FP);
          if (CurrStatus.count(FP)) {
            CurrStatus[FP] = static_cast<FatPtrCheckStatus>(
                static_cast<uint8_t>(CurrStatus[FP]) &
                static_cast<uint8_t>(FatPtrCheckStatus::KeyCheckedOnly));
          }
        }
      }
    }
  }
}

void TransferFunctions::VisitMemberExpr(MemberExpr *ME) {
  if (ME->isArrow()) {
    FatPtrVar FP;
    if (DeclRefExpr *DRE = getDREFromExpr(ME->getBase())) {
      if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
        FP = {VD, ""};
        if (VD->getType().isFatPtrType() && CurrStatus.count(FP)) {
          // Label the check kind in the sema phase, for member expression: p -> a;
          Ctx.FatPtrCheckStatusMap[DRE] = static_cast<uint8_t>(CurrStatus[FP]);
          // update the redundant check status
          CurrStatus[FP] = FatPtrCheckStatus::BothChecked;
        }
      }
    } else if (MemberExpr *SubME = getMemberExprFromExpr(ME->getBase())) {
      // handle p->a->b, if p->a is fat ptr.
      if (auto FD = dyn_cast<FieldDecl>(SubME->getMemberDecl())) {
        if (FD->getType().isFatPtrType()) {
          VisitMEForFieldPath(SubME, FP);
          if (CurrStatus.count(FP)) {
            Ctx.FatPtrCheckStatusMap[SubME] = static_cast<uint8_t>(CurrStatus[FP]);
            CurrStatus[FP] = FatPtrCheckStatus::BothChecked;
          }
        }
      }
    }
  }
}

// This function judge a user-defined functions in the
// current module may directly or indirectly frees heap memory.
// It conservertively assuems that a function call may free heap objects if it
//
//   1. is an indirect call that is not resolved by compiler or
//   2. calls to potentially unsafe functions
//
// For the second condition, we have a whitelist that contains all the functions
// that we are sure will not free memory, such as malloc. 

bool TransferFunctions::mayFreeCallExpr(CallExpr *CE) {
  // Check if it is an direct call, for indirect call, we assuems it may free
  if (FunctionDecl *CalleeDecl = CE->getDirectCallee()) {
    // Check if the function is in the whitelist
    if (MayFreeFnWL.find(CalleeDecl->getNameAsString()) != MayFreeFnWL.end()) {
      return false;
    }
    // Add the CalleeDecl to the call graph
    CG.addToCallGraph(CalleeDecl);
    CallGraphNode *Node = CG.getNode(CalleeDecl);
    // Current callee has no other function call in call graph
    if (!Node || Node->empty()) {
      // If there is no function definition, it is considered mayfree
      return !CalleeDecl->hasBody();
    } else {
      // Check if the CalleeDecl calls any function that may free heap objects
      bool mayFree = false;
      for (CallGraphNode::iterator It = Node->begin(), end = Node->end();
           It != end; ++It) {
        CallGraphNode *CalleeNode = It->Callee;
        if (!CalleeNode)
          continue;
        const FunctionDecl *CalleeFD =
            dyn_cast_or_null<FunctionDecl>(CalleeNode->getDecl());
        if (!CalleeFD || MayFreeFnWL.find(CalleeFD->getNameAsString()) == MayFreeFnWL.end()) {
          if (CalleeDecl->getNameAsString() != CalleeFD->getNameAsString()){
            mayFree = true;
            break;
          }
        }
      }
      return mayFree;
    }
  }
  return true;
}

// For mayfree function call, reset the check status to Unchecked for all the fat pointers
// More optimizations can be done here to reduce resets, including:
// 1. more accurate mayfree analysis
// 2. reset only some pointers through alias analysis.
void TransferFunctions::VisitCallExpr(CallExpr *CE) {
  // If the function call may free pointers, reset all fat pointers check status
  if (mayFreeCallExpr(CE)) {
    for (auto &Entry : CurrStatus) {
      Entry.second = FatPtrCheckStatus::Unchecked;
    }
    return;
  }

  // If the function call does not free pointers, check if the arguments are fat pointers
  for (unsigned i = 0; i < CE->getNumArgs(); i++) {
    Expr *Arg = CE->getArg(i)->IgnoreImpCasts();
    FatPtrVar FP;
    if (auto *DRE = dyn_cast<DeclRefExpr>(Arg)) {
      // If the argument is a fat pointer variable, change its check status to key only
      if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
        FP = {VD, ""};
        if (VD->getType().isFatPtrType() && CurrStatus.count(FP)) {
          CurrStatus[FP] = static_cast<FatPtrCheckStatus>(
              static_cast<uint8_t>(CurrStatus[FP]) &
              static_cast<uint8_t>(FatPtrCheckStatus::KeyCheckedOnly));
        }
      }
    } else if(auto *ME = dyn_cast<MemberExpr>(Arg)) {
      // handle func(p->a), if p->a is fat ptr.
      if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
        if (FD->getType().isFatPtrType()) {
          VisitMEForFieldPath(ME, FP);
          if (CurrStatus.count(FP)) {
            CurrStatus[FP] = static_cast<FatPtrCheckStatus>(
                static_cast<uint8_t>(CurrStatus[FP]) &
                static_cast<uint8_t>(FatPtrCheckStatus::KeyCheckedOnly));
          }
        }
      }
    }
  }
}

// Reset the redundant check status to BothChecked for the fat pointers
// which are used after CStyleCast.
void TransferFunctions::VisitCStyleCastExpr(CStyleCastExpr *CSCE) {
  FatPtrVar FP;
  if (DeclRefExpr *DRE = getDREFromExpr(CSCE->getSubExpr())) {
    if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
      FP = {VD, ""};
      if (VD->getType().isFatPtrType() && CurrStatus.count(FP)) {
        // Label the check kind in the sema phase, for CStyleCast expression: (int *)p;
        Ctx.FatPtrCheckStatusMap[DRE] = static_cast<uint8_t>(CurrStatus[FP]);
        // update the redundant check status
        CurrStatus[FP] = FatPtrCheckStatus::BothChecked;
      }
    }
  } else if (auto *ME = getMemberExprFromExpr(CSCE->getSubExpr())) {
    // handle (int *)(p->a), if p->a is fat ptr.
    if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
      if (FD->getType().isFatPtrType()) {
        VisitMEForFieldPath(ME, FP);
        if (CurrStatus.count(FP)) {
          Ctx.FatPtrCheckStatusMap[ME] = static_cast<uint8_t>(CurrStatus[FP]);
          CurrStatus[FP] = FatPtrCheckStatus::BothChecked;
        }
      }
    }
  }
}

void TransferFunctions::VisitArraySubscriptExpr(ArraySubscriptExpr *ASE) {
  FatPtrVar FP;
  if (DeclRefExpr *DRE = getDREFromExpr(ASE->getLHS())) {
    if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
      FP = {VD, ""};
      if (VD->getType().isFatPtrType() && CurrStatus.count(FP)) {
        // the offset check is not redundant, must be remained for array subscript expression: p[i];
        Ctx.FatPtrCheckStatusMap[DRE] =
            static_cast<uint8_t>(CurrStatus[FP]) &
            static_cast<uint8_t>(FatPtrCheckStatus::KeyCheckedOnly);
        // update the redundant check status to KeyCheckedOnly
        CurrStatus[FP] = FatPtrCheckStatus::BothChecked;
      }
    }
  } else if (auto *ME = getMemberExprFromExpr(ASE->getLHS())) {
    // handle p->a[i], if p->a is fat ptr.
    if (auto FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
      if (FD->getType().isFatPtrType()) {
        VisitMEForFieldPath(ME, FP);
        if (CurrStatus.count(FP)) {
          Ctx.FatPtrCheckStatusMap[ME] =
              static_cast<uint8_t>(CurrStatus[FP]) &
              static_cast<uint8_t>(FatPtrCheckStatus::KeyCheckedOnly);
          CurrStatus[FP] = FatPtrCheckStatus::BothChecked;
        }
      }
    }
  }
}

// Traverse all blocks of cfg to collect all fat pointers used,
// including local and global variable and parameters.
// Init check status of these pointers.
void FatPtrCheckImpl::initStatus(const CFG &cfg, ASTContext &ctx) {
  const CFGBlock *entry = &cfg.getEntry();
  for (const CFGBlock *B : cfg.const_nodes()) {
    if (B != entry && B != &cfg.getExit() && !B->succ_empty() &&
        !B->pred_empty()) {
      for (CFGBlock::const_iterator it = B->begin(), ei = B->end(); it != ei;
           ++it) {
        const CFGElement &elem = *it;
        if (elem.getAs<CFGStmt>()) {
          Stmt *S = const_cast<Stmt *>(elem.castAs<CFGStmt>().getStmt());
          FatPtrVar FP;
          if (auto DRE = dyn_cast<DeclRefExpr>(S)) {
            if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl()))
              if (VD->getType().isFatPtrType()) {
                FP = {VD, ""};
                BBOutStatus[entry][FP] = FatPtrCheckStatus::Unchecked;
              }
          } else if (auto ME = dyn_cast<MemberExpr>(S)) {
            if (FieldDecl *FD = dyn_cast<FieldDecl>(ME->getMemberDecl())) {
              if (FD->getType().isFatPtrType()) {
                VisitMEForFieldPath(ME, FP);
                BBOutStatus[entry][FP] = FatPtrCheckStatus::Unchecked;
              }
            }
          }
        }
      }
    }
  }
}

FatPtrVarCheckStatus
FatPtrCheckImpl::mergePredStatus(FatPtrVarCheckStatus currStatus,
                                 FatPtrVarCheckStatus predStatus) {
  if (currStatus.empty())
    return predStatus;
  for (auto predStatusOfFP : predStatus) {
    FatPtrVar FV = predStatusOfFP.first;
    FatPtrCheckStatus predKind = predStatusOfFP.second;
    if (currStatus.count(FV)) {
      FatPtrCheckStatus currKind = currStatus[FV];
      currStatus[FV] = static_cast<FatPtrCheckStatus>(
          static_cast<uint8_t>(currKind) & static_cast<uint8_t>(predKind));
    } else {
      currStatus[FV] = predKind;
    }
  }
  return currStatus;
}

FatPtrVarCheckStatus FatPtrCheckImpl::runOnBlock(const CFGBlock *block,
                                                 FatPtrVarCheckStatus &status,
                                                 ASTContext &ctx,
                                                 const FunctionDecl &fd,
                                                 ParentMap &PM) {
  TransferFunctions TF(*this, block, status, ctx, fd, PM);

  for (CFGBlock::const_iterator it = block->begin(), ei = block->end();
       it != ei; ++it) {
    const CFGElement &elem = *it;
    if (elem.getAs<CFGStmt>()) {
      const Stmt *S = elem.castAs<CFGStmt>().getStmt();
      TF.Visit(const_cast<Stmt *>(S));
    }
  }

  return status;
}

void clang::runFatPtrReduntantCheck(const FunctionDecl &fd, const CFG &cfg,
                                    AnalysisDeclContext &ac, ASTContext &ctx) {
  // The analysis currently has scalability issues for very large CFGs.
  // Bail out if it looks too large.
  if (cfg.getNumBlockIDs() > 300000)
    return;

  FatPtrCheckImpl FCI;
  FCI.initStatus(cfg, ctx);

  // Proceed with the worklist.
  ForwardDataflowWorklist worklist(cfg, ac);
  const CFGBlock *entry = &cfg.getEntry();
  for (const CFGBlock *B : cfg.const_reverse_nodes())
    if (B != entry && !B->pred_empty())
      worklist.enqueueBlock(B);

  while (const CFGBlock *block = worklist.dequeue()) {
    // record the last check status of the current block
    FatPtrVarCheckStatus lastCurrStatus = FCI.BBLastStatus[block];
    // get the check status of the pred block
    FatPtrVarCheckStatus currValStatus, predValStatus;
    for (CFGBlock::const_pred_iterator it = block->pred_begin(),
                                       ei = block->pred_end();
         it != ei; ++it) {
      if (const CFGBlock *pred = *it) {
        predValStatus = FCI.BBOutStatus[pred];
        currValStatus = FCI.mergePredStatus(currValStatus, predValStatus);
      }
    }

    FatPtrVarCheckStatus BBOutVal =
        FCI.runOnBlock(block, currValStatus, ctx, fd, ac.getParentMap());
    FCI.BBOutStatus[block] = BBOutVal;

    // If the value has changed, add the successors in the worklist.
    // For While-Stmt, the stmst in the block may change the redundant check status of some fat pointers.
    // So, it will be added into the worklist more than once until the analysis result remains unchanged.
    if (lastCurrStatus != BBOutVal) {
      FCI.BBLastStatus[block] = BBOutVal;
      worklist.enqueueSuccessors(block);
    }
  }
}

#endif
