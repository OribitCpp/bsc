//===- DeclBSC.h - Classes for representing BSC declarations --*- BSC -*-=====//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// Defines the BSC Decl subclasses
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_DECLBSC_H
#define LLVM_CLANG_AST_DECLBSC_H

#if ENABLE_BSC

#include "clang/AST/Decl.h"
#include "clang/AST/DeclBase.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/DeclarationName.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "clang/AST/TypeOrdering.h"

namespace clang {

class ASTContext;
class IdentifierInfo;
class UsingDecl;

class BSCMethodDecl : public FunctionDecl {
public:
  static BSCMethodDecl *
  Create(ASTContext &C, DeclContext *RD, SourceLocation StartLoc,
         const DeclarationNameInfo &NameInfo, QualType T, TypeSourceInfo *TInfo,
         StorageClass SC, bool UsesFPIntrin, bool isInline,
         ConstexprSpecKind ConstexprKind, SourceLocation EndLocation,
         Expr *TrailingRequiresClause = nullptr, bool isAsync = false);
  static BSCMethodDecl *CreateDeserialized(ASTContext &C, unsigned ID);

  bool getHasThisParam() const { return HasThisParam; }
  void setHasThisParam(bool HasThisParam) { this->HasThisParam = HasThisParam; }
  QualType getExtendedType() const { return ExtendedType; }
  void setExtendedType(QualType ExtendedType) {
    this->ExtendedType = ExtendedType;
  }

  /// Returns the start sourcelocation of extended type in BSCMethodDecl.
  SourceLocation getExtentedTypeBeginLoc() { return BLoc; }
  void setExtentedTypeBeginLoc(SourceLocation L) { BLoc = L; }

  bool isDestructor() const { return IsDestructor; }
  void setDestructor(bool flag) { this->IsDestructor = flag; }
  // Implement isa/cast/dyncast/etc.
  static bool classof(const Decl *D) { return classofKind(D->getKind()); }
  static bool classofKind(Kind K) { return K == BSCMethod; }

protected:
  BSCMethodDecl(Kind DK, ASTContext &C, DeclContext *RD,
                SourceLocation StartLoc, const DeclarationNameInfo &NameInfo,
                QualType T, TypeSourceInfo *TInfo, StorageClass SC,
                bool UsesFPIntrin, bool isInline,
                ConstexprSpecKind ConstexprKind, SourceLocation EndLocation,
                Expr *TrailingRequiresClause = nullptr, bool isAsync = false)
      : FunctionDecl(DK, C, RD, StartLoc, NameInfo, T, TInfo, SC, UsesFPIntrin,
                     isInline, ConstexprKind, TrailingRequiresClause, isAsync) {
    if (EndLocation.isValid())
      setRangeEnd(EndLocation);
  }

private:
  QualType ExtendedType;
  bool HasThisParam = false;
  SourceLocation BLoc;
  bool IsDestructor = false;
};

class TraitDecl : public TagDecl {
  RecordDecl *TraitR = nullptr;
  RecordDecl *OwnedTraitR = nullptr;
  RecordDecl *BorrowTraitR = nullptr;
  RecordDecl *Vtable = nullptr;
  std::map<QualType, VarDecl *, QualTypeOrdering> TypeImpled;

public:
  void MapInsert(QualType QT, VarDecl *VD) {
    TypeImpled.insert(std::pair<QualType, VarDecl *>(QT, VD));
  }

  VarDecl *getTypeImpledVarDecl(QualType QT) {
    std::map<QualType, VarDecl *, QualTypeOrdering>::iterator find;
    if (QT.isNull())
      return nullptr;
    find = TypeImpled.find(QT.getCanonicalType().getUnqualifiedType());
    if (find == TypeImpled.end())
      return nullptr;
    return find->second;
  }

  void dumpTypeImplMap() {
    for (auto i = TypeImpled.begin(); i != TypeImpled.end(); i++) {
      llvm::outs() << "[key]:\n";
      i->first->dump();
      llvm::outs() << "[value]:\n";
      i->second->dump();
    }
  }

  friend class DeclContext;
  llvm::PointerUnion<TraitTemplateDecl *, MemberSpecializationInfo *>
      TemplateOrInstantiation;

  static TraitDecl *Create(const ASTContext &C, DeclContext *DC,
                           SourceLocation StartLoc, SourceLocation IdLoc,
                           IdentifierInfo *Id, TraitDecl *PrevDecl = nullptr,
                           bool DelayTypeCreation = false);
  static TraitDecl *CreateDeserialized(ASTContext &C, unsigned ID);
  TraitDecl *getPreviousDecl() {
    return cast_or_null<TraitDecl>(
        static_cast<TagDecl *>(this)->getPreviousDecl());
  }
  const TraitDecl *getPreviousDecl() const {
    return const_cast<TraitDecl *>(this)->getPreviousDecl();
  }

  using field_iterator = specific_decl_iterator<FunctionDecl>;
  using field_range =
      llvm::iterator_range<specific_decl_iterator<FunctionDecl>>;

  field_range fields() const { return field_range(field_begin(), field_end()); }
  field_iterator field_begin() const;

  void setTrait(RecordDecl *RD) { TraitR = RD; }

  void setOwnedTrait(RecordDecl *RD) { OwnedTraitR = RD; }

  void setBorrowTrait(RecordDecl *RD) { BorrowTraitR = RD; }

  void setVtable(RecordDecl *RD) { Vtable = RD; }

  RecordDecl *getTrait() { return TraitR; }

  RecordDecl *getOwnedTrait() { return OwnedTraitR; }

  RecordDecl *getBorrowTrait() { return BorrowTraitR; }

  RecordDecl *getVtable() { return Vtable; }

  field_iterator field_end() const { return field_iterator(decl_iterator()); }

  bool field_empty() const { return field_begin() == field_end(); }

  virtual void completeDefinition();

  TraitDecl *getDefinition() const {
    return cast_or_null<TraitDecl>(TagDecl::getDefinition());
  }

  TraitTemplateDecl *getDescribedTraitTemplate() const;

  void setDescribedTraitTemplate(TraitTemplateDecl *Template);

  TemplateSpecializationKind getTemplateSpecializationKind() const;

  MemberSpecializationInfo *getMemberSpecializationInfo() const;

  bool isInjectedClassName() const;

  TraitDecl *getMostRecentDecl() {
    return cast<TraitDecl>(static_cast<TagDecl *>(this)->getMostRecentDecl());
  }

  const TraitDecl *getMostRecentDecl() const {
    return const_cast<TraitDecl *>(this)->getMostRecentDecl();
  }

  TraitDecl *getMostRecentNonInjectedDecl() {
    TraitDecl *Recent = static_cast<TraitDecl *>(this)->getMostRecentDecl();
    while (Recent->isInjectedClassName()) {
      // FIXME: Does injected class name need to be in the redeclarations chain?
      assert(Recent->getPreviousDecl());
      Recent = Recent->getPreviousDecl();
    }
    return Recent;
  }

  const TraitDecl *getMostRecentNonInjectedDecl() const {
    return const_cast<TraitDecl *>(this)->getMostRecentNonInjectedDecl();
  }

  static bool classof(const Decl *D) { return classofKind(D->getKind()); }
  static bool classofKind(Kind K) { return K >= firstTrait && K <= lastTrait; }

protected:
  TraitDecl(Kind DK, const ASTContext &C, DeclContext *DC,
            SourceLocation StartLoc, SourceLocation IdLoc, IdentifierInfo *Id,
            TraitDecl *PrevDecl);
};

class ImplTraitDecl : public DeclaratorDecl,
                      public Redeclarable<ImplTraitDecl> {
public:
  using redeclarable_base = Redeclarable<ImplTraitDecl>;
  using redeclarable_base::getMostRecentDecl;
  using redeclarable_base::getPreviousDecl;

  static ImplTraitDecl *Create(ASTContext &C, DeclContext *DC,
                               SourceLocation StartLoc, SourceLocation IdLoc,
                               IdentifierInfo *Id, QualType T,
                               TypeSourceInfo *TInfo, StorageClass S);

  static ImplTraitDecl *CreateDeserialized(ASTContext &C, unsigned ID);

  SourceRange getSourceRange() const override LLVM_READONLY;

  LanguageLinkage getLanguageLinkage() const;

  bool isInExternCContext() const;

  void setTraitDecl(TraitDecl *D);

  TraitDecl *getTraitDecl();

  ImplTraitDecl *getCanonicalDecl() override;

  static bool classof(const Decl *D) { return classofKind(D->getKind()); }

  static bool classofKind(Kind K) { return K == ImplTrait; }

protected:
  ImplTraitDecl(ASTContext &C, DeclContext *DC, SourceLocation StartLoc,
                SourceLocation IdLoc, IdentifierInfo *Id, QualType T,
                TypeSourceInfo *TInfo, StorageClass SC);

  ImplTraitDecl *getNextRedeclarationImpl() override {
    return getNextRedeclaration();
  }

  ImplTraitDecl *getPreviousDeclImpl() override { return getPreviousDecl(); }

  ImplTraitDecl *getMostRecentDeclImpl() override {
    return getMostRecentDecl();
  }

  TraitDecl *TD;
};

/// Declaration of a trait template.
class TraitTemplateDecl : public RedeclarableTemplateDecl {
public:
  friend class ASTDeclReader;
  friend class ASTDeclWriter;

  /// Load any lazily-loaded specializations from the external source.
  void LoadLazySpecializations() const;

  /// Get the underlying trait declarations of the template.
  TraitDecl *getTemplatedDecl() const {
    return static_cast<TraitDecl *>(TemplatedDecl);
  }

  /// Returns whether this template declaration defines the primary
  /// class pattern.
  bool isThisDeclarationADefinition() const {
    return getTemplatedDecl()->isThisDeclarationADefinition();
  }

  /// \brief Create a trait template node.
  static TraitTemplateDecl *Create(ASTContext &C, DeclContext *DC,
                                   SourceLocation L, DeclarationName Name,
                                   TemplateParameterList *Params,
                                   NamedDecl *Decl);

  /// Create an empty trait template node.
  static TraitTemplateDecl *CreateDeserialized(ASTContext &C, unsigned ID);

  TraitTemplateDecl *getMostRecentDecl() {
    return cast<TraitTemplateDecl>(
        static_cast<RedeclarableTemplateDecl *>(this)->getMostRecentDecl());
  }
  const TraitTemplateDecl *getMostRecentDecl() const {
    return const_cast<TraitTemplateDecl *>(this)->getMostRecentDecl();
  }

  /// Return the specialization with the provided arguments if it exists,
  /// otherwise return the insertion point.
  TraitTemplateSpecializationDecl *
  findSpecialization(ArrayRef<TemplateArgument> Args, void *&InsertPos);

  /// Insert the specified specialization knowing that it is not already
  /// in. InsertPos must be obtained from findSpecialization.
  void AddSpecialization(TraitTemplateSpecializationDecl *D, void *InsertPos);

  QualType getInjectedTraitNameSpecialization();

  using spec_iterator = SpecIterator<TraitTemplateSpecializationDecl>;
  using spec_range = llvm::iterator_range<spec_iterator>;

  spec_range specializations() const {
    return spec_range(spec_begin(), spec_end());
  }

  spec_iterator spec_begin() const {
    return makeSpecIterator(getSpecializations(), false);
  }

  spec_iterator spec_end() const {
    return makeSpecIterator(getSpecializations(), true);
  }

  // Implement isa/cast/dyncast support
  static bool classof(const Decl *D) { return classofKind(D->getKind()); }
  static bool classofKind(Kind K) { return K == TraitTemplate; }

protected:
  // Data that is common to all of the declarations of a given
  // trait template.
  struct Common : CommonBase {
    // The trait template specializations for this trait
    // template, including explicit specializations and instantiations.
    llvm::FoldingSetVector<TraitTemplateSpecializationDecl> Specializations;

    /// The trait template partial specializations for this trait
    /// template.
    llvm::FoldingSetVector<TraitTemplateSpecializationDecl>
        PartialSpecializations;

    // The injected-class-name type for this class template.
    QualType InjectedTraitNameType;

    Common() = default;
  };

  /// Retrieve the set of specializations of this class template.
  llvm::FoldingSetVector<TraitTemplateSpecializationDecl> &
  getSpecializations() const;

  /// Retrieve the set of partial specializations of this trait
  /// template.
  llvm::FoldingSetVector<TraitTemplateSpecializationDecl> &
  getPartialSpecializations() const;

  CommonBase *newCommon(ASTContext &C) const override;

  Common *getCommonPtr() const {
    return static_cast<Common *>(RedeclarableTemplateDecl::getCommonPtr());
  }

  TraitTemplateDecl(ASTContext &C, DeclContext *DC, SourceLocation L,
                    DeclarationName Name, TemplateParameterList *Params,
                    NamedDecl *Decl)
      : RedeclarableTemplateDecl(TraitTemplate, C, DC, L, Name, Params, Decl) {}
};

/// Represents a trait template specialization, which refers to
/// a trait template with a given set of template arguments.
///
/// Trait template specializations represent both explicit
/// specialization of trait templates, as in the example below, and
/// implicit instantiations of trait templates.
///
/// \code
/// trait X<T> {};
///
/// trait X<int>; // trait template specialization X<int>
/// \endcode
class TraitTemplateSpecializationDecl : public TraitDecl,
                                        public llvm::FoldingSetNode {
  /// Further info for explicit template specialization/instantiation.
  struct ExplicitSpecializationInfo {
    /// The type-as-written.
    TypeSourceInfo *TypeAsWritten = nullptr;

    /// The location of the extern keyword.
    SourceLocation ExternLoc;

    /// The location of the template keyword.
    SourceLocation TemplateKeywordLoc;

    ExplicitSpecializationInfo() = default;
  };

  /// Further info for explicit template specialization/instantiation.
  /// Does not apply to implicit specializations.
  ExplicitSpecializationInfo *ExplicitInfo = nullptr;

  /// The template that this specialization specializes.
  llvm::PointerUnion<TraitTemplateDecl *> SpecializedTemplate;

  /// The template arguments used to describe this specialization.
  const TemplateArgumentList *TemplateArgs;

  /// The point where this template was instantiated (if any)
  SourceLocation PointOfInstantiation;

  /// The kind of specialization this declaration refers to.
  /// Really a value of type TemplateSpecializationKind.
  unsigned SpecializationKind : 3;

public:
  friend class ASTDeclReader;
  friend class ASTDeclWriter;

  static TraitTemplateSpecializationDecl *
  Create(ASTContext &Context, TagKind TK, DeclContext *DC,
         SourceLocation StartLoc, SourceLocation IdLoc,
         TraitTemplateDecl *SpecializedTemplate,
         ArrayRef<TemplateArgument> Args,
         TraitTemplateSpecializationDecl *PrevDecl);
  static TraitTemplateSpecializationDecl *CreateDeserialized(ASTContext &C,
                                                             unsigned ID);

  TraitTemplateSpecializationDecl *getMostRecentDecl() {
    return cast<TraitTemplateSpecializationDecl>(
        getMostRecentNonInjectedDecl());
  }

  /// Retrieve the template arguments of the class template
  /// specialization.
  const TemplateArgumentList &getTemplateArgs() const { return *TemplateArgs; }

  void setTemplateArgs(TemplateArgumentList *Args) { TemplateArgs = Args; }

  /// Get the point of instantiation (if any), or null if none.
  SourceLocation getPointOfInstantiation() const {
    return PointOfInstantiation;
  }

  void setPointOfInstantiation(SourceLocation Loc) {
    assert(Loc.isValid() && "point of instantiation must be valid!");
    PointOfInstantiation = Loc;
  }

  TemplateSpecializationKind getSpecializationKind() const {
    return static_cast<TemplateSpecializationKind>(SpecializationKind);
  }

  void setTypeAsWritten(TypeSourceInfo *T) {
    if (!ExplicitInfo)
      ExplicitInfo = new (getASTContext()) ExplicitSpecializationInfo;
    ExplicitInfo->TypeAsWritten = T;
  }

  TypeSourceInfo *getTypeAsWritten() const {
    return ExplicitInfo ? ExplicitInfo->TypeAsWritten : nullptr;
  }

  /// Gets the location of the extern keyword, if present.
  SourceLocation getExternLoc() const {
    return ExplicitInfo ? ExplicitInfo->ExternLoc : SourceLocation();
  }

  /// Retrieve the template that this specialization specializes.
  TraitTemplateDecl *getSpecializedTemplate() const;

  SourceLocation getTemplateKeywordLoc() const {
    return ExplicitInfo ? ExplicitInfo->TemplateKeywordLoc : SourceLocation();
  }

  void Profile(llvm::FoldingSetNodeID &ID) const {
    Profile(ID, TemplateArgs->asArray(), getASTContext());
  }

  static void Profile(llvm::FoldingSetNodeID &ID,
                      ArrayRef<TemplateArgument> TemplateArgs,
                      ASTContext &Context) {
    ID.AddInteger(TemplateArgs.size());
    for (const TemplateArgument &TemplateArg : TemplateArgs)
      TemplateArg.Profile(ID, Context);
  }

  static bool classof(const Decl *D) { return classofKind(D->getKind()); }

  static bool classofKind(Kind K) { return K == TraitTemplateSpecialization; }

protected:
  TraitTemplateSpecializationDecl(ASTContext &Context, Kind DK, TagKind TK,
                                  DeclContext *DC, SourceLocation StartLoc,
                                  SourceLocation IdLoc,
                                  TraitTemplateDecl *SpecializedTemplate,
                                  ArrayRef<TemplateArgument> Args,
                                  TraitTemplateSpecializationDecl *PrevDecl);

  explicit TraitTemplateSpecializationDecl(ASTContext &C, Kind DK);
};

} // namespace clang

#endif // ENABLE_BSC

#endif // LLVM_CLANG_AST_DECLBSC_H