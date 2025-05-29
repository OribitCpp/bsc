//===- BSCBorrowCheck.h - Borrow Check for Source CFGs -*- BSC --*-------//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements BSC borrow check for source-level CFGs.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ANALYSIS_ANALYSES_BSCBORROWCHECK_H
#define LLVM_CLANG_ANALYSIS_ANALYSES_BSCBORROWCHECK_H

#if ENABLE_BSC
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Basic/DiagnosticSema.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Sema/Sema.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include <string>
#include <utility>

namespace clang {
enum BorrowKind : char {
  NoBorrow = 0,
  Mut,
  Immut,
};

struct BorrowTargetInfo {
  VarDecl *TargetVD = nullptr;
  std::string TargetFieldPath;
  bool TargetIsRawPointerOrItsField = false;

  BorrowTargetInfo() {}
  BorrowTargetInfo(VarDecl *targetVD, bool targetIsRawPointerOrItsField = false)
      : TargetVD(targetVD),
        TargetIsRawPointerOrItsField(targetIsRawPointerOrItsField) {}
  BorrowTargetInfo(VarDecl *targetVD, std::string targetFieldPath,
                   bool targetIsRawPointerOrItsField = false)
      : TargetVD(targetVD), TargetFieldPath(targetFieldPath),
        TargetIsRawPointerOrItsField(targetIsRawPointerOrItsField) {}

  bool operator==(const BorrowTargetInfo &Other) const {
    return TargetVD == Other.TargetVD &&
           TargetFieldPath == Other.TargetFieldPath &&
           TargetIsRawPointerOrItsField == Other.TargetIsRawPointerOrItsField;
  }
};

struct NonLexicalLifetimeRange {
  // If a borrow pointer comes from a struct, record the field path,
  // otherwise BorrowFieldPath will be void string.
  // For example,
  //     a.b.c = &mut local;  // BorrowFieldPath : ".b.c"
  //     p = &mut local;      // BorrowFieldPath : ""
  std::string BorrowFieldPath;

  unsigned Begin;
  unsigned End;
  BorrowKind Kind = BorrowKind::NoBorrow;

  // Record the target(VarDecl and FieldPath) of a borrow during this
  // NonLexicalLifetimeRange. For owned and other variables, TargetVD will be
  // void. Borrow from a variable, TargetFieldPath is void string; Borrow from a
  // member of a struct variable, TargetFieldPath records fields borrowed. For
  // example:
  //   int* borrow p1 = &mut local;     // TargetVD: local, TargetFieldPath: ""
  //   struct S* borrow p2 = &mut s;    // TargetVD: s,     TargetFieldPath: ""
  //   int* borrow p3 = &mut s.a;       // TargetVD: s,     TargetFieldPath: ".a"
  //   int* borrow p4 = &mut s.b.c;     // TargetVD: s,     TargetFieldPath: ".b.c"
  BorrowTargetInfo Target;

  NonLexicalLifetimeRange() {}

  // These constructors are for borrow variables, which have binding targets.
  NonLexicalLifetimeRange(unsigned begin, unsigned end, BorrowKind kind,
                          VarDecl *targetVD)
      : Begin(begin), End(end), Kind(kind), Target(BorrowTargetInfo(targetVD)) {
  }
  NonLexicalLifetimeRange(unsigned begin, unsigned end, BorrowKind kind,
                          BorrowTargetInfo target)
      : Begin(begin), End(end), Kind(kind), Target(target) {}
  NonLexicalLifetimeRange(unsigned begin, unsigned end, BorrowKind kind,
                          BorrowTargetInfo target, std::string borrowFieldPath)
      : BorrowFieldPath(borrowFieldPath), Begin(begin), End(end), Kind(kind),
        Target(target) {}

  // This constructor is for no-borrow variables, which don't have binding
  // targets.
  NonLexicalLifetimeRange(unsigned begin, unsigned end)
      : Begin(begin), End(end) {}

  bool operator==(const NonLexicalLifetimeRange &Other) const {
    return Begin == Other.Begin && End == Other.End && Kind == Other.Kind &&
           Target == Other.Target && BorrowFieldPath == Other.BorrowFieldPath;
  }
};

// NonLexicalLifetimeOfVar: NLL for a VarDecl in a cfg path.
using NonLexicalLifetimeOfVar = llvm::SmallVector<NonLexicalLifetimeRange>;

// NonLexicalLifetime: NLL for all variables in a cfg path.
// map<var, lifetime>:
//     var:
//         obj_var, owned_var, borrow_var
//     lifetime:
//         obj_lifetime: range
//         owned_lifetime: range
//         borrow_lifetime: vector<pair<range, target>>
using NonLexicalLifetime = llvm::DenseMap<VarDecl*, NonLexicalLifetimeOfVar>;

struct BorrowInfo {
  std::string TargetFieldPath;
  bool TargetIsRawPointerOrItsField;
  VarDecl *BorrowVD = nullptr;
  std::string BorrowFieldPath;
  unsigned Begin;
  unsigned End;
  BorrowKind Kind = BorrowKind::NoBorrow;
  bool Expired = false;

  BorrowInfo() {}
  BorrowInfo(std::string targetFieldPath, bool targetIsRawPointerOrItsField,
             VarDecl *borrowVD, std::string borrowFieldPath, unsigned begin,
             unsigned end, BorrowKind kind)
      : TargetFieldPath(targetFieldPath),
        TargetIsRawPointerOrItsField(targetIsRawPointerOrItsField),
        BorrowVD(borrowVD), BorrowFieldPath(borrowFieldPath), Begin(begin),
        End(end), Kind(kind) {}
  bool operator==(const BorrowInfo &other) {
    return TargetFieldPath == other.TargetFieldPath &&
           TargetIsRawPointerOrItsField == other.TargetIsRawPointerOrItsField &&
           BorrowVD == other.BorrowVD &&
           BorrowFieldPath == other.BorrowFieldPath && Begin == other.Begin &&
           End == other.End && Kind == other.Kind;
  }
};

using BorrowTargetMapInfo =
    llvm::DenseMap<VarDecl *, llvm::SmallVector<BorrowInfo>>;

enum BorrowCheckDiagKind {
  LiveLonger,
  AtMostOneMutBorrow,
  ReturnLocal,
  ModifyAfterBeBorrowed,
  ReadAfterBeMutBorrowed,
  UseExpiredBorrowVar,
};

struct BorrowCheckDiagInfo {
  std::string Name;
  BorrowCheckDiagKind Kind;
  SourceLocation Loc;
  SourceLocation PreLoc;

  BorrowCheckDiagInfo(std::string Name, BorrowCheckDiagKind Kind,
                      SourceLocation Loc,
                      SourceLocation PreLoc = SourceLocation())
      : Name(Name), Kind(Kind), Loc(Loc), PreLoc(PreLoc) {}

  bool operator==(const BorrowCheckDiagInfo& other) const {
    return Name == other.Name &&
           Kind == other.Kind &&
           Loc == other.Loc;
  }
};

class BorrowCheckDiagReporter {
  Sema &S;
  std::vector<BorrowCheckDiagInfo> DIV;

public:
  BorrowCheckDiagReporter(Sema &S) : S(S) {}
  ~BorrowCheckDiagReporter() { flushDiagnostics(); }

  void addDiagInfo(BorrowCheckDiagInfo &DI) {
    for (auto it = DIV.begin(), ei = DIV.end();
          it != ei; ++it) {
      if (DI == *it)
        return;
    }
    DIV.push_back(DI);
  }

private:
  void flushDiagnostics() {
    // Sort the diag info by their SourceLocations. While not strictly
    // guaranteed to produce them in line/column order, this will provide
    // a stable ordering.
    std::sort(
        DIV.begin(), DIV.end(),
        [this](const BorrowCheckDiagInfo &a, const BorrowCheckDiagInfo &b) {
          return S.getSourceManager().isBeforeInTranslationUnit(a.Loc, b.Loc);
        });

    for (const BorrowCheckDiagInfo &DI : DIV) {
      switch (DI.Kind) {
        case LiveLonger:
          S.Diag(DI.Loc, diag::err_borrow_live_longer_than_target_var) << DI.Name;
          break;
        case AtMostOneMutBorrow:
          S.Diag(DI.Loc, diag::err_at_most_one_mut_borrow) << DI.Name;
          S.Diag(DI.PreLoc, diag::note_previous_borrow);
          break;
        case ReturnLocal:
          S.Diag(DI.Loc, diag::err_return_value_borrow_local) << DI.Name;
          break;
        case ModifyAfterBeBorrowed:
          S.Diag(DI.Loc, diag::err_modify_after_be_borrow) << DI.Name;
          S.Diag(DI.PreLoc, diag::note_previous_borrow);
          break;
        case ReadAfterBeMutBorrowed:
          S.Diag(DI.Loc, diag::err_read_after_be_mut_borrow) << DI.Name;
          S.Diag(DI.PreLoc, diag::note_previous_borrow);
          break;
        case UseExpiredBorrowVar:
          S.Diag(DI.Loc, diag::err_use_expired_borrow_var) << DI.Name;
          break;
        default:
          llvm_unreachable("unknown error type");
          break;
      }
      S.getDiagnostics().increaseBorrowCheckErrors();
    }
  }
};

void runBorrowCheck(const FunctionDecl &fd, const CFG &cfg,
                    BorrowCheckDiagReporter &reporter, ASTContext& Ctx);

} // end namespace clang

#endif // ENABLE_BSC

#endif // LLVM_CLANG_ANALYSIS_ANALYSES_BSCBORROWCHECK_H