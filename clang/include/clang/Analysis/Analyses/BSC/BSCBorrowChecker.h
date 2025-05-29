//===- BSCBorrowChecker.h - Borrow Check for Source CFGs -*- BSC --*----------//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements BSC borrow checker for source-level CFGs.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ANALYSIS_ANALYSES_BSCBORROWCHECKER_H
#define LLVM_CLANG_ANALYSIS_ANALYSES_BSCBORROWCHECKER_H

#if ENABLE_BSC

#include "clang/AST/Decl.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/DiagnosticSema.h"
#include "clang/Sema/Sema.h"
#include <set>
#include <unordered_map>

#define DEBUG_PRINT 0

namespace clang {
namespace borrow {
class RegionCheck;

/// Name of region. Each RegionName corresponds to an AST node.
///
/// Each bound region is named `'region` plus a positive integer,
/// such as 'region_0, 'region_1, etc. Bound region is related to
/// variables or a borrow/reborrow expression in the function.
/// The free region is named 'region_r. Free region is related to
/// the return point in the function or points in the caller.
class RegionName {
private:
  RegionName(std::string Name) : Name(Name) {}

public:
  std::string Name;
  constexpr static const char *const NamePrefix = "'region_";
  static unsigned Cnt;

  bool operator<(const RegionName &other) const { return Name < other.Name; }

  static RegionName Create() {
    return RegionName(NamePrefix + std::to_string(Cnt++));
  }

  static RegionName CreateFree() {
    return RegionName(std::string(NamePrefix) + "r");
  }

  RegionName() { Name = "invalid"; }

  bool isInvalid() const { return Name == "invalid"; }

  std::string print() const { return "RegionName { " + Name + " }"; }
};

/// An index representation of RegionName, in order to facilitate calculations.
///
/// Each RegionName corresponds to a RegionVariable.
/// The index of RegionVariable increases from 0.
struct RegionVariable {
  unsigned index;

  RegionVariable(unsigned index = 0) : index(index) {}

  std::string print() const {
    return "RegionVariable { index: " + std::to_string(index) + " }";
  }
};

/// Representation of variables and fields of structs.
///
/// Examples:
///
/// - the Path of `a` is:
///     Path(Var, "a").
/// - the Path of `p.a` is:
///     Path(Extension,
///          Path(Var, "p"),
///          "a").
/// - the Path of `p->a` is:
///     Path(Extension,
///          Path(Extension,
///               Path(Var, "p"),
///               "*"),
///          "a").
/// - the Path of `*p.a` is:
///     Path(Extension,
///          Path(Extension,
///               Path(Var, "p"),
///               "a"),
///          "*").
/// - the Path of `*(p->a)` is:
///     Path(Extension,
///          Path(Extension,
///               Path(Extension,
///                    Path(Var, "p"),
///                    "*"),
///               "a"),
///          "*").
/// - the Path of `p->a->b` is:
///     Path(Extension,
///          Path(Extension,
///               Path(Extension,
///                    Path(Extension,
///                         Path(Var, "p"),
///                         "*"),
///                    "a"),
///               "*"),
///          "b").
struct Path {
  enum class PathType : unsigned char { Var, Extension };

  PathType type;

  // Non-null when type is Extension.
  std::unique_ptr<Path> base = nullptr;

  std::string fieldName;

  // Type of the current path.
  QualType ty;

  // Need for reborrow constraints generation.
  Decl *D = nullptr;

  SourceLocation Location;

  /// Construct a Var type Path.
  explicit Path(const std::string &name, QualType ty, SourceLocation Location)
      : type(PathType::Var), fieldName(name), ty(ty), Location(Location) {}

  // Construct an Extension type Path.
  Path(std::unique_ptr<Path> base, const std::string &name, QualType ty,
       SourceLocation Location)
      : type(PathType::Extension), base(std::move(base)), fieldName(name),
        ty(ty), Location(Location) {}

  Path(const Path &other)
      : type(other.type), fieldName(other.fieldName), ty(other.ty), D(other.D),
        Location(other.Location) {
    if (other.base) {
      base = std::make_unique<Path>(*other.base);
    }
  }

  ~Path() = default;

  void setDecl(Decl *D) { this->D = D; }

  bool isDeref() const {
    if (type == PathType::Var)
      return false;
    return fieldName == "*";
  }

  /// The prefixes of a path are all the lvalues you get by stripping away
  /// fields and derefs.
  ///
  /// Examples:
  ///
  /// - the prefixes of `*a.b` where `a` is a struct are
  ///   `*a.b`, `a.b` and `a`.
  /// - the prefixes of `a.b.c` where both `a` and `b` are structs are
  ///   `a.b.c`, `a.b` and `a`.
  llvm::SmallVector<const Path *> prefixes() const {
    llvm::SmallVector<const Path *> result;
    const Path *cur = this;
    while (true) {
      result.push_back(cur);
      if (cur->type == PathType::Var)
        return result;
      cur = cur->base.get();
    }
  }

  /// The supporting prefixes of a path are all the prefixes of a path that
  /// must remain valid for the path itself to remain valid. For the most part,
  /// this means all prefixes, except that recursion stops when dereferencing a
  /// shared reference.
  ///
  /// Examples:
  ///
  /// - the supporting prefixes of `s.f` where `s` is a struct are
  ///   `s.f` and `s`.
  /// - the supporting prefixes of `(*r).f` where `r` is a shared reference are
  ///   `(*r).f` and `*r`, but not `r`.
  ///   - Intuition: one could always copy `*r` into a temporary `t` and reach
  ///     the data through `*t`, so it is not important to preserve `r` itself.
  /// - the supporting prefixes of `(*m).f` where `m` is a mutable reference are
  ///   `(*m).f`, `*m`, and `m`.
  llvm::SmallVector<const Path *> supportingPrefixes() const {
    llvm::SmallVector<const Path *> result;
    const Path *cur = this;
    while (true) {
      result.push_back(cur);
      if (cur->type == PathType::Var)
        return result;
      if (cur->fieldName == "*" && cur->base->ty.isConstBorrow()) {
        return result;
      }
      cur = cur->base.get();
    }
  }

  std::string to_string() const {
    if (type == PathType::Var)
      return fieldName;
    if (fieldName == "*")
      return "*" + base->to_string();
    if (base->isDeref())
      return '(' + base->to_string() + ")." + fieldName;
    return base->to_string() + '.' + fieldName;
  }

  std::string print() const { return to_string(); }
};

enum class BorrowKind { Mut, Shared };

/// An abstraction of CFG nodes.
///
/// Every CFG node is converted to one or more actions.
struct Action {
  enum ActionKind { Noop, Init, Borrow, Assign, Use, StorageDead };

  ActionKind Kind;

  Action(ActionKind Kind) : Kind(Kind) {}

  virtual ~Action() = default;

  ActionKind getKind() const { return Kind; }

  virtual llvm::Optional<const Path *> OverWrites() const { return llvm::None; }

  virtual std::string print() const = 0;

private:
  virtual void anchor();
};

/// ActionNoop represents statement that does not use any variables.
struct ActionNoop : public Action {
  ActionNoop() : Action(Noop) {}

  ~ActionNoop() override = default;

  std::string print() const override { return "ActionNoop"; }

  static bool classof(const Action *A) { return A->getKind() == Noop; }

private:
  void anchor() override;
};

/// ActionInit represents a variable declaration or assignment statement.
///
/// Note that the declared or assigned variable is of a non-borrow type.
struct ActionInit : public Action {
  std::unique_ptr<Path> Dest;
  std::vector<std::unique_ptr<Path>> Sources;
  std::vector<std::unique_ptr<Path>> DerefSources;

  ActionInit(std::unique_ptr<Path> Dest,
             std::vector<std::unique_ptr<Path>> Sources,
             std::vector<std::unique_ptr<Path>> DerefSources = {})
      : Action(Init), Dest(std::move(Dest)), Sources(std::move(Sources)),
        DerefSources(std::move(DerefSources)) {}

  ~ActionInit() override = default;

  virtual llvm::Optional<const Path *> OverWrites() const override {
    return llvm::Optional<const Path *>(Dest.get());
  }

  std::string print() const override {
    std::string Ret;
    Ret += "ActionInit: ";
    Ret += Dest->print();
    Ret += " = use(";
    for (auto &a : Sources) {
      Ret += a->print();
      Ret += ", ";
    }
    Ret += ")";
    return Ret;
  }

  static bool classof(const Action *A) { return A->getKind() == Init; }

private:
  void anchor() override;
};

/// ActionBorrow represents a statement that explicity borrows a variable using
/// `&mut`, `&const`, `&mut *`, or `&const *`.
struct ActionBorrow : public Action {
  std::unique_ptr<Path> Dest;
  RegionName RNL;
  RegionName RNR;
  BorrowKind BK;
  std::unique_ptr<Path> Source;

  ActionBorrow(std::unique_ptr<Path> Dest, RegionName RNL, RegionName RNR,
               BorrowKind BK, std::unique_ptr<Path> Source)
      : Action(Borrow), Dest(std::move(Dest)), RNL(RNL), RNR(RNR), BK(BK),
        Source(std::move(Source)) {}

  ~ActionBorrow() override = default;

  virtual llvm::Optional<const Path *> OverWrites() const override {
    return llvm::Optional<const Path *>(Dest.get());
  }

  std::string print() const override {
    std::string Ret;
    Ret += "ActionBorrow: ";
    Ret += Dest->print();
    Ret += " = ";
    Ret += RNR.Name;
    if (BK == BorrowKind::Mut)
      Ret += " &mut ";
    else
      Ret += " & ";
    Ret += Source->print();
    return Ret;
  }

  static bool classof(const Action *A) { return A->getKind() == Borrow; }

private:
  void anchor() override;
};

/// ActionAssign represents an assignment between variables of borrow types.
struct ActionAssign : public Action {
  std::unique_ptr<Path> Dest;
  RegionName RNL;
  RegionName RNR;
  std::unique_ptr<Path> Source;
  RegionName DerefRN;
  std::vector<std::unique_ptr<Path>> DerefSources;

  ActionAssign(std::unique_ptr<Path> Dest, RegionName RNL, RegionName RNR,
               std::unique_ptr<Path> Source, RegionName DerefRN,
               std::vector<std::unique_ptr<Path>> DerefSources)
      : Action(Assign), Dest(std::move(Dest)), RNL(RNL), RNR(RNR),
        Source(std::move(Source)), DerefRN(DerefRN),
        DerefSources(std::move(DerefSources)) {}

  ~ActionAssign() override = default;

  virtual llvm::Optional<const Path *> OverWrites() const override {
    return llvm::Optional<const Path *>(Dest.get());
  }

  std::string print() const override {
    std::string Ret;
    Ret += "ActionAssign: ";
    Ret += Dest->print();
    Ret += " " + RNL.print();
    Ret += " = ";
    Ret += Source->print();
    Ret += " " + RNR.print();
    return Ret;
  }

  static bool classof(const Action *A) { return A->getKind() == Assign; }

private:
  void anchor() override;
};

/// ActionUse represents the usage of a vairble, including reading, writing, or
/// transferring its ownership.
struct ActionUse : public Action {
  std::vector<std::unique_ptr<Path>> Uses;
  std::vector<std::unique_ptr<Path>> DerefSources;

  ActionUse(std::vector<std::unique_ptr<Path>> Uses,
            std::vector<std::unique_ptr<Path>> DerefSources)
      : Action(Use), Uses(std::move(Uses)),
        DerefSources(std::move(DerefSources)) {}

  ~ActionUse() override = default;

  std::string print() const override {
    std::string Ret;
    Ret += "ActionUse: ";
    Ret += " use(";
    for (auto &a : Uses) {
      Ret += a->print();
      Ret += ", ";
    }
    Ret += ")";
    return Ret;
  }

  static bool classof(const Action *A) { return A->getKind() == Use; }

private:
  void anchor() override;
};

/// ActionStorageDead represents leaving the lexical scope of a variable,
/// meaning it is destroyed on the stack.
struct ActionStorageDead : public Action {
  std::unique_ptr<Path> Var;

  ActionStorageDead(std::unique_ptr<Path> Var)
      : Action(StorageDead), Var(std::move(Var)) {}

  ~ActionStorageDead() override = default;

  std::string print() const override {
    std::string Ret;
    Ret += "ActionStorageDead: ";
    Ret += Var->print();
    return Ret;
  }

  static bool classof(const Action *A) { return A->getKind() == StorageDead; }

private:
  void anchor() override;
};

/// Represents the position of nodes in the cfg.
///
/// `blockID` represents the index of the basic block, and `index` represents
/// the index of node in the current basic block.
struct Point {
  unsigned blockID;
  unsigned index;

  /// Indicates the `End('region_r)` of free region `'region_r`.
  static const unsigned EndBlockID = -1u;
  static const unsigned EndIndex = -1u;

  Point(unsigned blockID, unsigned index) : blockID(blockID), index(index) {}

  bool operator<(const Point &other) const {
    if (this->blockID != other.blockID)
      return this->blockID < other.blockID;
    return this->index < other.index;
  }

  std::string print() const {
    if (blockID == EndBlockID && index == EndIndex)
      return "End('region_r)";
    return "BB" + std::to_string(blockID) + '/' + std::to_string(index);
  }
};

/// Represents the region scope of a region variable, consisting a series
/// points in the CFG.
struct Region {
  std::set<Point> points;

  bool AddPoint(Point P) {
    auto Ret = points.insert(P);
    return Ret.second;
  }

  bool MayContain(Point P) const { return points.find(P) != points.end(); }

  std::string print() const {
    std::string Ret = "{ ";
    unsigned index = 0;
    for (const Point &point : points) {
      Ret += point.print();
      if (index != points.size() - 1)
        Ret += ", ";
      ++index;
    }
    Ret += " }";
    return Ret;
  }
};

/// A complete definition of a region variable, consisting of the corresponding
/// region name, region scope and a capped flag.
///
/// Note that each region variable corresponds to a VarDecl or an explicit or
/// implicit borrow expression.
struct VarDefinition {
  RegionName name;

  /// The current value of this region name. This is adjusted during region
  /// check by calls to `AddLivePoint`, and then finally adjusted further by
  /// the call to `Solve`.
  Region value;

  /// Capped region names should no longer have to grow as a result of
  /// inference. If they do wind up growing, we will report an error.
  bool capped;

  VarDefinition(RegionName name, Region value, bool capped)
      : name(name), value(value), capped(capped) {}
};

/// The constraint indicates `sub` outlives `sup` at `point`.
struct Constraint {
  RegionVariable sub;
  RegionVariable sup;
  Point point;

  Constraint(RegionVariable sub, RegionVariable sup, Point point)
      : sub(sub), sup(sup), point(point) {}

  std::string print() const {
    return "Constraint { " + sub.print() + " : " + sup.print() + " @ " +
           point.print() + " }" + '\n';
  }
};

class Environment {
public:
  const FunctionDecl &fd;
  const CFG &cfg;
  const ASTContext &Ctx;

public:
  Environment(const FunctionDecl &fd, const CFG &cfg, const ASTContext &Ctx)
      : fd(fd), cfg(cfg), Ctx(Ctx) {}

  llvm::SmallVector<Point> SuccessorPoints(Point point) const;
};

/// All the information required for inference solving, including the
/// definition of region variables and all the constraints in the function.
class InferenceContext {
private:
  llvm::SmallVector<VarDefinition> definitions;
  llvm::SmallVector<Constraint> constraints;

  /// Used for implicit borrows.
  Region emptyRegion;

public:
  InferenceContext() {}

  RegionVariable AddVar(RegionName Name) {
    size_t index = definitions.size();
#if DEBUG_PRINT
    llvm::outs() << Name.print() << " => " << RegionVariable(index).print()
                 << '\n';
#endif
    definitions.push_back(VarDefinition(Name, Region(), false));
    return RegionVariable(index);
  }

  void CapVar(RegionVariable RV) { definitions[RV.index].capped = true; }

  void AddLivePoint(RegionVariable RV, Point P);

  void AddOutLives(RegionVariable Sup, RegionVariable Sub, Point P) {
#if DEBUG_PRINT
    llvm::outs() << "AddOutLives: " << Sub.print() << " : " << Sup.print()
                 << " @ " << P.print() << '\n';
#endif
    constraints.push_back(Constraint(Sub, Sup, P));
  }

  const Region &getRegion(RegionVariable RV) const {
    return definitions[RV.index].value;
  }

  const Region &getEmptyRegion() const { return emptyRegion; }

  void Solve(const Environment &env);
};

class DFS {
private:
  llvm::SmallVector<Point, 4> stack;
  std::set<Point> visited;
  const Environment &env;

public:
  DFS(const Environment &env) : env(env) {}

  bool Copy(const Region &From, Region &To, Point StartPoint);
};

/// Compute the set of live variables at each point.
class Liveness {
private:
  using LivenessFact = llvm::DenseSet<VarDecl *>;

  const Environment &env;
  RegionCheck &rc;

  /// For a given key, which is a basic block, the value is the set of all live
  /// variables at the entry of the block.
  llvm::DenseMap<const CFGBlock *, LivenessFact> liveness;

  void Kill(LivenessFact &fact, VarDecl *D) { fact.erase(D); }

  void Gen(LivenessFact &fact, VarDecl *D) { fact.insert(D); }

  bool SetFrom(LivenessFact &Dest, const LivenessFact &Src) {
    if (Src.empty())
      return false;

    unsigned old = Dest.size();
    Dest.insert(Src.begin(), Src.end());
    return old != Dest.size();
  }

  template <typename CB>
  void SimulateBlock(LivenessFact &fact, const CFGBlock *Block, CB callback);

public:
  Liveness(const Environment &env, RegionCheck &rc) : env(env), rc(rc) {
    Compute();
  }

  void Compute();

  template <typename CB> void Walk(CB callback);

  std::set<RegionName> LiveRegions(const LivenessFact &liveFact);

  void print() const {
    llvm::outs() << "Liveness Result: \n";
    for (auto elem : liveness) {
      llvm::outs() << "CFG Block ID: " << elem.first->getBlockID() << '\n';
      llvm::outs() << "Live Variables at block entry: \n";
      for (VarDecl *var : elem.second) {
        llvm::outs() << var->getName() << '\t';
      }
      llvm::outs() << '\n';
    }
  }
};

struct Loan {
  Point point;
  const std::unique_ptr<Path> &path;
  BorrowKind kind;
  const Region &region;

  Loan(Point point, const std::unique_ptr<Path> &path, BorrowKind kind,
       const Region &region)
      : point(point), path(path), kind(kind), region(region) {}

  std::string print() const {
    std::string Ret;
    Ret += "  Loan {\n";
    Ret += "    point: " + point.print() + "\n";
    Ret += "    path: " + path->print() + "\n";
    Ret += "    kind: ";
    if (kind == BorrowKind::Mut)
      Ret += "Mut\n";
    else
      Ret += "Shared\n";
    Ret += "    region: " + region.print() + "\n";
    Ret += "  }";
    return Ret;
  }
};

class LoansInScope {
private:
  using LoansFact = llvm::DenseSet<unsigned>;

  const Environment &env;
  const RegionCheck &rc;

  /// All loans in the function.
  llvm::SmallVector<Loan> loans;

  llvm::DenseMap<const CFGBlock *, LoansFact> loansInScopeAfterBlock;

  /// For a given key, which is a point of the CFG, the value is a vector of
  /// the index of all loans at the entry of the point.
  std::map<Point, std::vector<unsigned>> loansByPoint;

  void Kill(LoansFact &fact, unsigned index) { fact.erase(index); }

  void Gen(LoansFact &fact, std::vector<unsigned> indexes) {
    fact.insert(indexes.begin(), indexes.end());
  }

  bool SetFrom(LoansFact &Dest, const LoansFact &Src) {
    if (Src.empty())
      return false;

    unsigned old = Dest.size();
    Dest.insert(Src.begin(), Src.end());
    return old != Dest.size();
  }

  llvm::SmallVector<unsigned> LoansNotInScopeAt(Point point) const {
    llvm::SmallVector<unsigned> ret;
    for (const Loan *it = loans.begin(), *ei = loans.end(); it != ei; ++it) {
      if (!it->region.MayContain(point))
        ret.push_back(std::distance(loans.begin(), it));
    }
    return ret;
  }

  llvm::SmallVector<unsigned> LoansKilledByWriteTo(const Path *path) const;

  template <typename CB>
  void SimulateBlock(LoansFact &fact, const CFGBlock *Block, CB callback);

public:
  LoansInScope(const Environment &env, const RegionCheck &rc);

  void Compute();

  template <typename CB> void Walk(CB callback);
};

enum class Depth { Shallow, Deep };

enum class Mode { Read, Write };

enum class BorrowDiagKind {
  ForImmutWhenMut,
  ForMove,
  ForMultiMut,
  ForMutWhenImmut,
  ForRead,
  ForWrite,
  ForStorageDead,
  BorrowMaxDiagKind
};

const unsigned BorrowDiagIdList[] = {
    diag::err_borrow_immut_borrow_when_mut_borrowed,
    diag::err_borrow_move_when_borrowed,
    diag::err_borrow_mut_borrow_more_than_once,
    diag::err_borrow_mut_borrow_when_immut_borrowed,
    diag::err_borrow_use_when_mut_borrowed,
    diag::err_borrow_not_live_long,
    diag::err_borrow_assign_when_borrowed};

struct BorrowDiagInfo {
  BorrowDiagKind Kind;
  SourceLocation Location;
  std::string path;
  SourceLocation LoanLoc;
  std::string loanPath;

  BorrowDiagInfo(BorrowDiagKind Kind, SourceLocation Location, std::string path,
                 SourceLocation LoanLoc, std::string loanPath = "")
      : Kind(Kind), Location(Location), path(path), LoanLoc(LoanLoc),
        loanPath(loanPath) {}
};

class BorrowDiagReporter {
private:
  Sema &S;
  llvm::SmallVector<BorrowDiagInfo> Infos;

  void flushDiagnostics() {
    for (BorrowDiagInfo Info : Infos) {
      switch (Info.Kind) {
      case BorrowDiagKind::ForImmutWhenMut:
        S.Diag(Info.Location, diag::err_borrow_immut_borrow_when_mut_borrowed)
            << Info.path;
        S.Diag(Info.LoanLoc, diag::note_mutable_borrow_occurs_here);
        break;
      case BorrowDiagKind::ForMove:
        S.Diag(Info.Location, diag::err_borrow_move_when_borrowed) << Info.path;
        S.Diag(Info.LoanLoc, diag::note_borrowed_here) << Info.loanPath;
        break;
      case BorrowDiagKind::ForMultiMut:
        S.Diag(Info.Location, diag::err_borrow_mut_borrow_more_than_once)
            << Info.path;
        S.Diag(Info.LoanLoc, diag::note_first_mut_borrow_occurs_here);
        break;
      case BorrowDiagKind::ForMutWhenImmut:
        S.Diag(Info.Location, diag::err_borrow_mut_borrow_when_immut_borrowed)
            << Info.path;
        S.Diag(Info.LoanLoc, diag::note_immutable_borrow_occurs_here);
        break;
      case BorrowDiagKind::ForRead:
        S.Diag(Info.Location, diag::err_borrow_use_when_mut_borrowed)
            << Info.path;
        S.Diag(Info.LoanLoc, diag::note_borrowed_here) << Info.loanPath;
        break;
      case BorrowDiagKind::ForStorageDead:
        S.Diag(Info.Location, diag::err_borrow_not_live_long) << Info.path;
        S.Diag(Info.LoanLoc, diag::note_dropped_while_borrowed) << Info.path;
        break;
      case BorrowDiagKind::ForWrite:
        S.Diag(Info.Location, diag::err_borrow_assign_when_borrowed)
            << Info.path;
        S.Diag(Info.LoanLoc, diag::note_borrowed_here) << Info.path;
        break;
      default:
        break;
      }
      S.getDiagnostics().increaseBorrowCheckErrors();
    }
  }

public:
  BorrowDiagReporter(Sema &S) : S(S) {}

  ~BorrowDiagReporter() { flushDiagnostics(); }

  void ForImmutWhenMut(SourceLocation Location, const Path *path,
                       SourceLocation LoanLoc) {
    Infos.push_back(BorrowDiagInfo(BorrowDiagKind::ForImmutWhenMut, Location,
                                   path->to_string(), LoanLoc));
  }

  void ForMove(SourceLocation Location, const Path *path,
               SourceLocation LoanLoc, const Path *loanPath) {
    Infos.push_back(BorrowDiagInfo(BorrowDiagKind::ForMove, Location,
                                   path->to_string(), LoanLoc,
                                   loanPath->to_string()));
  }

  void ForMultiMut(SourceLocation Location, const Path *path,
                   SourceLocation LoanLoc) {
    Infos.push_back(BorrowDiagInfo(BorrowDiagKind::ForMultiMut, Location,
                                   path->to_string(), LoanLoc));
  }

  void ForMutWhenImmut(SourceLocation Location, const Path *path,
                       SourceLocation LoanLoc) {
    Infos.push_back(BorrowDiagInfo(BorrowDiagKind::ForMutWhenImmut, Location,
                                   path->to_string(), LoanLoc));
  }

  void ForRead(SourceLocation Location, const Path *path,
               SourceLocation LoanLoc, const Path *loanPath) {
    Infos.push_back(BorrowDiagInfo(BorrowDiagKind::ForRead, Location,
                                   path->to_string(), LoanLoc,
                                   loanPath->to_string()));
  }

  void ForStorageDead(SourceLocation Location, const Path *path,
                      SourceLocation LoanLoc) {
    Infos.push_back(BorrowDiagInfo(BorrowDiagKind::ForStorageDead, LoanLoc,
                                   path->to_string(), Location));
  }

  void ForWrite(SourceLocation Location, const Path *path,
                SourceLocation LoanLoc) {
    Infos.push_back(BorrowDiagInfo(BorrowDiagKind::ForWrite, Location,
                                   path->to_string(), LoanLoc));
  }

  unsigned getBorrowDiagID(BorrowDiagKind Kind) {
    unsigned index = static_cast<unsigned>(Kind);
    assert(index < static_cast<unsigned>(BorrowDiagKind::BorrowMaxDiagKind) &&
           "Unknown error type");
    return BorrowDiagIdList[index];
  }

  void emitDiag(BorrowDiagKind Kind, SourceLocation Location, const Path *path,
                SourceLocation LoanLoc, const Path *loanPath = nullptr) {
    if (S.getDiagnostics().getDiagnosticLevel(
            getBorrowDiagID(Kind), Location) == DiagnosticsEngine::Ignored) {
      return;
    }
    switch (Kind) {
    case BorrowDiagKind::ForImmutWhenMut:
      ForImmutWhenMut(Location, path, LoanLoc);
      break;
    case BorrowDiagKind::ForMove:
      ForMove(Location, path, LoanLoc, loanPath);
      break;
    case BorrowDiagKind::ForMultiMut:
      ForMultiMut(Location, path, LoanLoc);
      break;
    case BorrowDiagKind::ForMutWhenImmut:
      ForMutWhenImmut(Location, path, LoanLoc);
      break;
    case BorrowDiagKind::ForRead:
      ForRead(Location, path, LoanLoc, loanPath);
      break;
    case BorrowDiagKind::ForStorageDead:
      ForStorageDead(Location, path, LoanLoc);
      break;
    case BorrowDiagKind::ForWrite:
      ForWrite(Location, path, LoanLoc);
      break;
    default:
      break;
    }
  }
};

class BorrowCheck {
private:
  BorrowDiagReporter &reporter;
  const Environment &env;
  Point point;
  const llvm::SmallVector<Loan> &loans;
  bool IsBorrow = false;

  void CheckBorrows(Depth depth, Mode accessMode,
                    const std::unique_ptr<Path> &path);
  void CheckMove(const std::unique_ptr<Path> &path);
  void CheckMutBorrow(const std::unique_ptr<Path> &path);
  void CheckRead(const std::unique_ptr<Path> &path);
  void CheckShallowWrite(const std::unique_ptr<Path> &path);
  void CheckStorageDead(const std::unique_ptr<Path> &path);

  llvm::SmallVector<const Loan *>
  FindLoansThatFreeze(const std::unique_ptr<Path> &path);
  llvm::SmallVector<const Loan *>
  FindLoansThatIntersect(const std::unique_ptr<Path> &path);
  llvm::SmallVector<const Path *>
  FrozenByBorrowOf(const std::unique_ptr<Path> &path);

public:
  BorrowCheck(BorrowDiagReporter &reporter, const Environment &env, Point point,
              const llvm::SmallVector<Loan> &loans)
      : reporter(reporter), env(env), point(point), loans(loans) {}

  void CheckAction(const std::unique_ptr<Action> &action);
};

class RegionCheck {
private:
  BorrowDiagReporter &reporter;
  Environment env;
  InferenceContext infer;
  std::unordered_map<Decl *, RegionName> declToRegionNameMap;
  std::unordered_map<Stmt *, RegionName> stmtToRegionNameMap;
  std::map<RegionName, RegionVariable> regionMap;
  std::map<Point, std::vector<std::unique_ptr<Action>>> actionMap;

  void PopulateInference(Liveness &liveness);
  RegionVariable getRegionVariable(RegionName RV);
  void EnsureBorrowSource(Point SuccPoint, RegionName BorrowRegionName,
                          const std::unique_ptr<Path> &SourcePath);
  void RelateRegions(Point SuccPoint, RegionName Sub, RegionName Sup);
  void PreprocessForParamAndReturn();

public:
  RegionCheck(const FunctionDecl &fd, const CFG &cfg, ASTContext &Ctx,
              BorrowDiagReporter &Reporter)
      : reporter(Reporter), env(fd, cfg, Ctx) {}

  void Check();

  /// Get the corresponding RegionName for a Decl in the regionMap.
  /// If not existing, create a RegionName and return it.
  RegionName getRegionName(Decl *D);

  /// Get the corresponding RegionName for a Stmt in the regionMap.
  /// If not existing, create a RegionName and return it.
  RegionName getRegionName(Stmt *S);

  const Region &getRegion(RegionName RN) const;

  const Region &getEmptyRegion() const { return infer.getEmptyRegion(); }

  BorrowDiagReporter &getReporter() { return reporter; }

  const std::map<Point, std::vector<std::unique_ptr<Action>>> &
  getActionMap() const {
    return actionMap;
  }
};

void BorrowCk(const Environment &env, RegionCheck &rc, LoansInScope &LIS);
void runBorrowChecker(const FunctionDecl &fd, const CFG &cfg, ASTContext &Ctx,
                      BorrowDiagReporter &Reporter);

} // end namespace borrow
} // end namespace clang

#endif // ENABLE_BSC

#endif // LLVM_CLANG_ANALYSIS_ANALYSES_BSCBORROWCHECKER_H