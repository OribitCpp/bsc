//===- ASTWriter.h - AST File Writer ----------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file defines the ASTWriter class, which writes an AST file
//  containing a serialized representation of a translation unit.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_SERIALIZATION_ASTWRITER_H
#define LLVM_CLANG_SERIALIZATION_ASTWRITER_H

#include "clang/AST/ASTMutationListener.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Type.h"
#include "clang/Basic/LLVM.h"
#include "clang/Basic/Module.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/SemaConsumer.h"
#include "clang/Serialization/ASTBitCodes.h"
#include "clang/Serialization/ASTDeserializationListener.h"
#include "clang/Serialization/PCHContainerOperations.h"
#include "clang/Serialization/SourceLocationEncoding.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Bitstream/BitstreamWriter.h"
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <ctime>
#include <memory>
#include <queue>
#include <string>
#include <utility>
#include <vector>

namespace clang {

class ASTContext;
class ASTReader;
class Attr;
class CXXRecordDecl;
class FileEntry;
class FPOptionsOverride;
class FunctionDecl;
class HeaderSearch;
class HeaderSearchOptions;
class IdentifierResolver;
class LangOptions;
class MacroDefinitionRecord;
class MacroInfo;
class Module;
class InMemoryModuleCache;
class ModuleFileExtension;
class ModuleFileExtensionWriter;
class NamedDecl;
class ObjCInterfaceDecl;
class PreprocessingRecord;
class Preprocessor;
class RecordDecl;
class Sema;
class SourceManager;
class Stmt;
class StoredDeclsList;
class SwitchCase;
class Token;

/// Writes an AST file containing the contents of a translation unit.
///
/// The ASTWriter class produces a bitstream containing the serialized
/// representation of a given abstract syntax tree and its supporting
/// data structures. This bitstream can be de-serialized via an
/// instance of the ASTReader class.
class ASTWriter : public ASTDeserializationListener,
                  public ASTMutationListener {
public:
  friend class ASTDeclWriter;
  friend class ASTRecordWriter;

  using RecordData = SmallVector<uint64_t, 64>;
  using RecordDataImpl = SmallVectorImpl<uint64_t>;
  using RecordDataRef = ArrayRef<uint64_t>;

private:
  /// Map that provides the ID numbers of each type within the
  /// output stream, plus those deserialized from a chained PCH.
  ///
  /// The ID numbers of types are consecutive (in order of discovery)
  /// and start at 1. 0 is reserved for NULL. When types are actually
  /// stored in the stream, the ID number is shifted by 2 bits to
  /// allow for the const/volatile qualifiers.
  ///
  /// Keys in the map never have const/volatile qualifiers.
  using TypeIdxMap = llvm::DenseMap<QualType, serialization::TypeIdx,
                                    serialization::UnsafeQualTypeDenseMapInfo>;

  using LocSeq = SourceLocationSequence;

  /// The bitstream writer used to emit this precompiled header.
  llvm::BitstreamWriter &Stream;

  /// The buffer associated with the bitstream.
  const SmallVectorImpl<char> &Buffer;

  /// The PCM manager which manages memory buffers for pcm files.
  InMemoryModuleCache &ModuleCache;

  /// The ASTContext we're writing.
  ASTContext *Context = nullptr;

  /// The preprocessor we're writing.
  Preprocessor *PP = nullptr;

  /// The reader of existing AST files, if we're chaining.
  ASTReader *Chain = nullptr;

  /// The module we're currently writing, if any.
  Module *WritingModule = nullptr;

  /// The offset of the first bit inside the AST_BLOCK.
  uint64_t ASTBlockStartOffset = 0;

  /// The range representing all the AST_BLOCK.
  std::pair<uint64_t, uint64_t> ASTBlockRange;

  /// The base directory for any relative paths we emit.
  std::string BaseDirectory;

  /// Indicates whether timestamps should be written to the produced
  /// module file. This is the case for files implicitly written to the
  /// module cache, where we need the timestamps to determine if the module
  /// file is up to date, but not otherwise.
  bool IncludeTimestamps;

  /// Indicates when the AST writing is actively performing
  /// serialization, rather than just queueing updates.
  bool WritingAST = false;

  /// Indicates that we are done serializing the collection of decls
  /// and types to emit.
  bool DoneWritingDeclsAndTypes = false;

  /// Indicates that the AST contained compiler errors.
  bool ASTHasCompilerErrors = false;

  /// Mapping from input file entries to the index into the
  /// offset table where information about that input file is stored.
  llvm::DenseMap<const FileEntry *, uint32_t> InputFileIDs;

  /// Stores a declaration or a type to be written to the AST file.
  class DeclOrType {
  public:
    DeclOrType(Decl *D) : Stored(D), IsType(false) {}
    DeclOrType(QualType T) : Stored(T.getAsOpaquePtr()), IsType(true) {}

    bool isType() const { return IsType; }
    bool isDecl() const { return !IsType; }

    QualType getType() const {
      assert(isType() && "Not a type!");
      return QualType::getFromOpaquePtr(Stored);
    }

    Decl *getDecl() const {
      assert(isDecl() && "Not a decl!");
      return static_cast<Decl *>(Stored);
    }

  private:
    void *Stored;
    bool IsType;
  };

  /// The declarations and types to emit.
  std::queue<DeclOrType> DeclTypesToEmit;

  /// The first ID number we can use for our own declarations.
  serialization::DeclID FirstDeclID = serialization::NUM_PREDEF_DECL_IDS;

  /// The decl ID that will be assigned to the next new decl.
  serialization::DeclID NextDeclID = FirstDeclID;

  /// Map that provides the ID numbers of each declaration within
  /// the output stream, as well as those deserialized from a chained PCH.
  ///
  /// The ID numbers of declarations are consecutive (in order of
  /// discovery) and start at 2. 1 is reserved for the translation
  /// unit, while 0 is reserved for NULL.
  llvm::DenseMap<const Decl *, serialization::DeclID> DeclIDs;

  /// Offset of each declaration in the bitstream, indexed by
  /// the declaration's ID.
  std::vector<serialization::DeclOffset> DeclOffsets;

  /// The offset of the DECLTYPES_BLOCK. The offsets in DeclOffsets
  /// are relative to this value.
  uint64_t DeclTypesBlockStartOffset = 0;

  /// Sorted (by file offset) vector of pairs of file offset/DeclID.
  using LocDeclIDsTy =
      SmallVector<std::pair<unsigned, serialization::DeclID>, 64>;
  struct DeclIDInFileInfo {
    LocDeclIDsTy DeclIDs;

    /// Set when the DeclIDs vectors from all files are joined, this
    /// indicates the index that this particular vector has in the global one.
    unsigned FirstDeclIndex;
  };
  using FileDeclIDsTy =
      llvm::DenseMap<FileID, std::unique_ptr<DeclIDInFileInfo>>;

  /// Map from file SLocEntries to info about the file-level declarations
  /// that it contains.
  FileDeclIDsTy FileDeclIDs;

  void associateDeclWithFile(const Decl *D, serialization::DeclID);

  /// The first ID number we can use for our own types.
  serialization::TypeID FirstTypeID = serialization::NUM_PREDEF_TYPE_IDS;

  /// The type ID that will be assigned to the next new type.
  serialization::TypeID NextTypeID = FirstTypeID;

  /// Map that provides the ID numbers of each type within the
  /// output stream, plus those deserialized from a chained PCH.
  ///
  /// The ID numbers of types are consecutive (in order of discovery)
  /// and start at 1. 0 is reserved for NULL. When types are actually
  /// stored in the stream, the ID number is shifted by 2 bits to
  /// allow for the const/volatile qualifiers.
  ///
  /// Keys in the map never have const/volatile qualifiers.
  TypeIdxMap TypeIdxs;

  /// Offset of each type in the bitstream, indexed by
  /// the type's ID.
  std::vector<serialization::UnderalignedInt64> TypeOffsets;

  /// The first ID number we can use for our own identifiers.
  serialization::IdentID FirstIdentID = serialization::NUM_PREDEF_IDENT_IDS;

  /// The identifier ID that will be assigned to the next new identifier.
  serialization::IdentID NextIdentID = FirstIdentID;

  /// Map that provides the ID numbers of each identifier in
  /// the output stream.
  ///
  /// The ID numbers for identifiers are consecutive (in order of
  /// discovery), starting at 1. An ID of zero refers to a NULL
  /// IdentifierInfo.
  llvm::MapVector<const IdentifierInfo *, serialization::IdentID> IdentifierIDs;

  /// The first ID number we can use for our own macros.
  serialization::MacroID FirstMacroID = serialization::NUM_PREDEF_MACRO_IDS;

  /// The identifier ID that will be assigned to the next new identifier.
  serialization::MacroID NextMacroID = FirstMacroID;

  /// Map that provides the ID numbers of each macro.
  llvm::DenseMap<MacroInfo *, serialization::MacroID> MacroIDs;

  struct MacroInfoToEmitData {
    const IdentifierInfo *Name;
    MacroInfo *MI;
    serialization::MacroID ID;
  };

  /// The macro infos to emit.
  std::vector<MacroInfoToEmitData> MacroInfosToEmit;

  llvm::DenseMap<const IdentifierInfo *, uint32_t>
      IdentMacroDirectivesOffsetMap;

  /// @name FlushStmt Caches
  /// @{

  /// Set of parent Stmts for the currently serializing sub-stmt.
  llvm::DenseSet<Stmt *> ParentStmts;

  /// Offsets of sub-stmts already serialized. The offset points
  /// just after the stmt record.
  llvm::DenseMap<Stmt *, uint64_t> SubStmtEntries;

  /// @}

  /// Offsets of each of the identifier IDs into the identifier
  /// table.
  std::vector<uint32_t> IdentifierOffsets;

  /// The first ID number we can use for our own submodules.
  serialization::SubmoduleID FirstSubmoduleID =
      serialization::NUM_PREDEF_SUBMODULE_IDS;

  /// The submodule ID that will be assigned to the next new submodule.
  serialization::SubmoduleID NextSubmoduleID = FirstSubmoduleID;

  /// The first ID number we can use for our own selectors.
  serialization::SelectorID FirstSelectorID =
      serialization::NUM_PREDEF_SELECTOR_IDS;

  /// The selector ID that will be assigned to the next new selector.
  serialization::SelectorID NextSelectorID = FirstSelectorID;

  /// Map that provides the ID numbers of each Selector.
  llvm::MapVector<Selector, serialization::SelectorID> SelectorIDs;

  /// Offset of each selector within the method pool/selector
  /// table, indexed by the Selector ID (-1).
  std::vector<uint32_t> SelectorOffsets;

  /// Mapping from macro definitions (as they occur in the preprocessing
  /// record) to the macro IDs.
  llvm::DenseMap<const MacroDefinitionRecord *,
                 serialization::PreprocessedEntityID> MacroDefinitions;

  /// Cache of indices of anonymous declarations within their lexical
  /// contexts.
  llvm::DenseMap<const Decl *, unsigned> AnonymousDeclarationNumbers;

  /// An update to a Decl.
  class DeclUpdate {
    /// A DeclUpdateKind.
    unsigned Kind;
    union {
      const Decl *Dcl;
      void *Type;
      SourceLocation::UIntTy Loc;
      unsigned Val;
      Module *Mod;
      const Attr *Attribute;
    };

  public:
    DeclUpdate(unsigned Kind) : Kind(Kind), Dcl(nullptr) {}
    DeclUpdate(unsigned Kind, const Decl *Dcl) : Kind(Kind), Dcl(Dcl) {}
    DeclUpdate(unsigned Kind, QualType Type)
        : Kind(Kind), Type(Type.getAsOpaquePtr()) {}
    DeclUpdate(unsigned Kind, SourceLocation Loc)
        : Kind(Kind), Loc(Loc.getRawEncoding()) {}
    DeclUpdate(unsigned Kind, unsigned Val) : Kind(Kind), Val(Val) {}
    DeclUpdate(unsigned Kind, Module *M) : Kind(Kind), Mod(M) {}
    DeclUpdate(unsigned Kind, const Attr *Attribute)
          : Kind(Kind), Attribute(Attribute) {}

    unsigned getKind() const { return Kind; }
    const Decl *getDecl() const { return Dcl; }
    QualType getType() const { return QualType::getFromOpaquePtr(Type); }

    SourceLocation getLoc() const {
      return SourceLocation::getFromRawEncoding(Loc);
    }

    unsigned getNumber() const { return Val; }
    Module *getModule() const { return Mod; }
    const Attr *getAttr() const { return Attribute; }
  };

  using UpdateRecord = SmallVector<DeclUpdate, 1>;
  using DeclUpdateMap = llvm::MapVector<const Decl *, UpdateRecord>;

  /// Mapping from declarations that came from a chained PCH to the
  /// record containing modifications to them.
  DeclUpdateMap DeclUpdates;

  using FirstLatestDeclMap = llvm::DenseMap<Decl *, Decl *>;

  /// Map of first declarations from a chained PCH that point to the
  /// most recent declarations in another PCH.
  FirstLatestDeclMap FirstLatestDecls;

  /// Declarations encountered that might be external
  /// definitions.
  ///
  /// We keep track of external definitions and other 'interesting' declarations
  /// as we are emitting declarations to the AST file. The AST file contains a
  /// separate record for these declarations, which are provided to the AST
  /// consumer by the AST reader. This is behavior is required to properly cope with,
  /// e.g., tentative variable definitions that occur within
  /// headers. The declarations themselves are stored as declaration
  /// IDs, since they will be written out to an EAGERLY_DESERIALIZED_DECLS
  /// record.
  SmallVector<serialization::DeclID, 16> EagerlyDeserializedDecls;
  SmallVector<serialization::DeclID, 16> ModularCodegenDecls;

  /// DeclContexts that have received extensions since their serialized
  /// form.
  ///
  /// For namespaces, when we're chaining and encountering a namespace, we check
  /// if its primary namespace comes from the chain. If it does, we add the
  /// primary to this set, so that we can write out lexical content updates for
  /// it.
  llvm::SmallSetVector<const DeclContext *, 16> UpdatedDeclContexts;

  /// Keeps track of declarations that we must emit, even though we're
  /// not guaranteed to be able to find them by walking the AST starting at the
  /// translation unit.
  SmallVector<const Decl *, 16> DeclsToEmitEvenIfUnreferenced;

  /// The set of Objective-C class that have categories we
  /// should serialize.
  llvm::SetVector<ObjCInterfaceDecl *> ObjCClassesWithCategories;

  /// The set of declarations that may have redeclaration chains that
  /// need to be serialized.
  llvm::SmallVector<const Decl *, 16> Redeclarations;

  /// A cache of the first local declaration for "interesting"
  /// redeclaration chains.
  llvm::DenseMap<const Decl *, const Decl *> FirstLocalDeclCache;

  /// Mapping from SwitchCase statements to IDs.
  llvm::DenseMap<SwitchCase *, unsigned> SwitchCaseIDs;

  /// The number of statements written to the AST file.
  unsigned NumStatements = 0;

  /// The number of macros written to the AST file.
  unsigned NumMacros = 0;

  /// The number of lexical declcontexts written to the AST
  /// file.
  unsigned NumLexicalDeclContexts = 0;

  /// The number of visible declcontexts written to the AST
  /// file.
  unsigned NumVisibleDeclContexts = 0;

  /// A mapping from each known submodule to its ID number, which will
  /// be a positive integer.
  llvm::DenseMap<const Module *, unsigned> SubmoduleIDs;

  /// A list of the module file extension writers.
  std::vector<std::unique_ptr<ModuleFileExtensionWriter>>
      ModuleFileExtensionWriters;

  /// User ModuleMaps skipped when writing control block.
  std::set<const FileEntry *> SkippedModuleMaps;

  /// Retrieve or create a submodule ID for this module.
  unsigned getSubmoduleID(Module *Mod);

  /// Write the given subexpression to the bitstream.
  void WriteSubStmt(Stmt *S);

  void WriteBlockInfoBlock();
  void WriteControlBlock(Preprocessor &PP, ASTContext &Context,
                         StringRef isysroot, const std::string &OutputFile);

  /// Write out the signature and diagnostic options, and return the signature.
  ASTFileSignature writeUnhashedControlBlock(Preprocessor &PP,
                                             ASTContext &Context);

  /// Calculate hash of the pcm content.
  static std::pair<ASTFileSignature, ASTFileSignature>
  createSignature(StringRef AllBytes, StringRef ASTBlockBytes);

  void WriteInputFiles(SourceManager &SourceMgr, HeaderSearchOptions &HSOpts,
                       std::set<const FileEntry *> &AffectingModuleMaps);
  void WriteSourceManagerBlock(SourceManager &SourceMgr,
                               const Preprocessor &PP);
  void writeIncludedFiles(raw_ostream &Out, const Preprocessor &PP);
  void WritePreprocessor(const Preprocessor &PP, bool IsModule);
  void WriteHeaderSearch(const HeaderSearch &HS);
  void WritePreprocessorDetail(PreprocessingRecord &PPRec,
                               uint64_t MacroOffsetsBase);
  void WriteSubmodules(Module *WritingModule);

  void WritePragmaDiagnosticMappings(const DiagnosticsEngine &Diag,
                                     bool isModule);

  unsigned TypeExtQualAbbrev = 0;
  void WriteTypeAbbrevs();
  void WriteType(QualType T);

  bool isLookupResultExternal(StoredDeclsList &Result, DeclContext *DC);
  bool isLookupResultEntirelyExternal(StoredDeclsList &Result, DeclContext *DC);

  void GenerateNameLookupTable(const DeclContext *DC,
                               llvm::SmallVectorImpl<char> &LookupTable);
  uint64_t WriteDeclContextLexicalBlock(ASTContext &Context, DeclContext *DC);
  uint64_t WriteDeclContextVisibleBlock(ASTContext &Context, DeclContext *DC);
  void WriteTypeDeclOffsets();
  void WriteFileDeclIDsMap();
  void WriteComments();
  void WriteSelectors(Sema &SemaRef);
  void WriteReferencedSelectorsPool(Sema &SemaRef);
  void WriteIdentifierTable(Preprocessor &PP, IdentifierResolver &IdResolver,
                            bool IsModule);
  void WriteDeclUpdatesBlocks(RecordDataImpl &OffsetsRecord);
  void WriteDeclContextVisibleUpdate(const DeclContext *DC);
  void WriteFPPragmaOptions(const FPOptionsOverride &Opts);
  void WriteOpenCLExtensions(Sema &SemaRef);
  void WriteCUDAPragmas(Sema &SemaRef);
  void WriteObjCCategories();
  void WriteLateParsedTemplates(Sema &SemaRef);
  void WriteOptimizePragmaOptions(Sema &SemaRef);
  void WriteMSStructPragmaOptions(Sema &SemaRef);
  void WriteMSPointersToMembersPragmaOptions(Sema &SemaRef);
  void WritePackPragmaOptions(Sema &SemaRef);
  void WriteFloatControlPragmaOptions(Sema &SemaRef);
  void WriteModuleFileExtension(Sema &SemaRef,
                                ModuleFileExtensionWriter &Writer);

  unsigned DeclParmVarAbbrev = 0;
  unsigned DeclContextLexicalAbbrev = 0;
  unsigned DeclContextVisibleLookupAbbrev = 0;
  unsigned UpdateVisibleAbbrev = 0;
  unsigned DeclRecordAbbrev = 0;
  unsigned DeclTypedefAbbrev = 0;
  unsigned DeclVarAbbrev = 0;
  unsigned DeclFieldAbbrev = 0;
  unsigned DeclEnumAbbrev = 0;
  #if ENABLE_BSC
  unsigned DeclTraitAbbrev = 0;
  unsigned DeclImplTraitAbbrev = 0;
  #endif
  unsigned DeclObjCIvarAbbrev = 0;
  unsigned DeclCXXMethodAbbrev = 0;
  #if ENABLE_BSC
  unsigned DeclBSCMethodAbbrev = 0;
  #endif

  unsigned DeclRefExprAbbrev = 0;
  unsigned CharacterLiteralAbbrev = 0;
  unsigned IntegerLiteralAbbrev = 0;
  unsigned ExprImplicitCastAbbrev = 0;

  void WriteDeclAbbrevs();
  void WriteDecl(ASTContext &Context, Decl *D);

  ASTFileSignature WriteASTCore(Sema &SemaRef, StringRef isysroot,
                                const std::string &OutputFile,
                                Module *WritingModule);

public:
  /// Create a new precompiled header writer that outputs to
  /// the given bitstream.
  ASTWriter(llvm::BitstreamWriter &Stream, SmallVectorImpl<char> &Buffer,
            InMemoryModuleCache &ModuleCache,
            ArrayRef<std::shared_ptr<ModuleFileExtension>> Extensions,
            bool IncludeTimestamps = true);
  ~ASTWriter() override;

  ASTContext &getASTContext() const {
    assert(Context && "requested AST context when not writing AST");
    return *Context;
  }

  const LangOptions &getLangOpts() const;

  /// Get a timestamp for output into the AST file. The actual timestamp
  /// of the specified file may be ignored if we have been instructed to not
  /// include timestamps in the output file.
  time_t getTimestampForOutput(const FileEntry *E) const;

  /// Write a precompiled header for the given semantic analysis.
  ///
  /// \param SemaRef a reference to the semantic analysis object that processed
  /// the AST to be written into the precompiled header.
  ///
  /// \param WritingModule The module that we are writing. If null, we are
  /// writing a precompiled header.
  ///
  /// \param isysroot if non-empty, write a relocatable file whose headers
  /// are relative to the given system root. If we're writing a module, its
  /// build directory will be used in preference to this if both are available.
  ///
  /// \return the module signature, which eventually will be a hash of
  /// the module but currently is merely a random 32-bit number.
  ASTFileSignature WriteAST(Sema &SemaRef, const std::string &OutputFile,
                            Module *WritingModule, StringRef isysroot,
                            bool hasErrors = false,
                            bool ShouldCacheASTInMemory = false);

  /// Emit a token.
  void AddToken(const Token &Tok, RecordDataImpl &Record);

  /// Emit a AlignPackInfo.
  void AddAlignPackInfo(const Sema::AlignPackInfo &Info,
                        RecordDataImpl &Record);

  /// Emit a source location.
  void AddSourceLocation(SourceLocation Loc, RecordDataImpl &Record,
                         LocSeq *Seq = nullptr);

  /// Emit a source range.
  void AddSourceRange(SourceRange Range, RecordDataImpl &Record,
                      LocSeq *Seq = nullptr);

  /// Emit a reference to an identifier.
  void AddIdentifierRef(const IdentifierInfo *II, RecordDataImpl &Record);

  /// Get the unique number used to refer to the given selector.
  serialization::SelectorID getSelectorRef(Selector Sel);

  /// Get the unique number used to refer to the given identifier.
  serialization::IdentID getIdentifierRef(const IdentifierInfo *II);

  /// Get the unique number used to refer to the given macro.
  serialization::MacroID getMacroRef(MacroInfo *MI, const IdentifierInfo *Name);

  /// Determine the ID of an already-emitted macro.
  serialization::MacroID getMacroID(MacroInfo *MI);

  uint32_t getMacroDirectivesOffset(const IdentifierInfo *Name);

  /// Emit a reference to a type.
  void AddTypeRef(QualType T, RecordDataImpl &Record);

  /// Force a type to be emitted and get its ID.
  serialization::TypeID GetOrCreateTypeID(QualType T);

  /// Determine the type ID of an already-emitted type.
  serialization::TypeID getTypeID(QualType T) const;

  /// Find the first local declaration of a given local redeclarable
  /// decl.
  const Decl *getFirstLocalDecl(const Decl *D);

  /// Is this a local declaration (that is, one that will be written to
  /// our AST file)? This is the case for declarations that are neither imported
  /// from another AST file nor predefined.
  bool IsLocalDecl(const Decl *D) {
    if (D->isFromASTFile())
      return false;
    auto I = DeclIDs.find(D);
    return (I == DeclIDs.end() ||
            I->second >= serialization::NUM_PREDEF_DECL_IDS);
  };

  /// Emit a reference to a declaration.
  void AddDeclRef(const Decl *D, RecordDataImpl &Record);

  /// Force a declaration to be emitted and get its ID.
  serialization::DeclID GetDeclRef(const Decl *D);

  /// Determine the declaration ID of an already-emitted
  /// declaration.
  serialization::DeclID getDeclID(const Decl *D);

  unsigned getAnonymousDeclarationNumber(const NamedDecl *D);

  /// Add a string to the given record.
  void AddString(StringRef Str, RecordDataImpl &Record);

  /// Convert a path from this build process into one that is appropriate
  /// for emission in the module file.
  bool PreparePathForOutput(SmallVectorImpl<char> &Path);

  /// Add a path to the given record.
  void AddPath(StringRef Path, RecordDataImpl &Record);

  /// Emit the current record with the given path as a blob.
  void EmitRecordWithPath(unsigned Abbrev, RecordDataRef Record,
                          StringRef Path);

  /// Add a version tuple to the given record
  void AddVersionTuple(const VersionTuple &Version, RecordDataImpl &Record);

  /// Retrieve or create a submodule ID for this module, or return 0 if
  /// the submodule is neither local (a submodle of the currently-written module)
  /// nor from an imported module.
  unsigned getLocalOrImportedSubmoduleID(const Module *Mod);

  /// Note that the identifier II occurs at the given offset
  /// within the identifier table.
  void SetIdentifierOffset(const IdentifierInfo *II, uint32_t Offset);

  /// Note that the selector Sel occurs at the given offset
  /// within the method pool/selector table.
  void SetSelectorOffset(Selector Sel, uint32_t Offset);

  /// Record an ID for the given switch-case statement.
  unsigned RecordSwitchCaseID(SwitchCase *S);

  /// Retrieve the ID for the given switch-case statement.
  unsigned getSwitchCaseID(SwitchCase *S);

  void ClearSwitchCaseIDs();

  unsigned getTypeExtQualAbbrev() const {
    return TypeExtQualAbbrev;
  }

  unsigned getDeclParmVarAbbrev() const { return DeclParmVarAbbrev; }
  unsigned getDeclRecordAbbrev() const { return DeclRecordAbbrev; }
  unsigned getDeclTypedefAbbrev() const { return DeclTypedefAbbrev; }
  unsigned getDeclVarAbbrev() const { return DeclVarAbbrev; }
  unsigned getDeclFieldAbbrev() const { return DeclFieldAbbrev; }
  unsigned getDeclEnumAbbrev() const { return DeclEnumAbbrev; }
  #if ENABLE_BSC
  unsigned getDeclTraitAbbrev() const { return DeclTraitAbbrev; }
  unsigned getDeclImplTraitAbbrev() const { return DeclImplTraitAbbrev; }
  #endif
  unsigned getDeclObjCIvarAbbrev() const { return DeclObjCIvarAbbrev; }
  unsigned getDeclCXXMethodAbbrev() const { return DeclCXXMethodAbbrev; }
  #if ENABLE_BSC
  unsigned getDeclBSCMethodAbbrev() const { return DeclBSCMethodAbbrev; }
  #endif

  unsigned getDeclRefExprAbbrev() const { return DeclRefExprAbbrev; }
  unsigned getCharacterLiteralAbbrev() const { return CharacterLiteralAbbrev; }
  unsigned getIntegerLiteralAbbrev() const { return IntegerLiteralAbbrev; }
  unsigned getExprImplicitCastAbbrev() const { return ExprImplicitCastAbbrev; }

  bool hasChain() const { return Chain; }
  ASTReader *getChain() const { return Chain; }

  bool isWritingNamedModules() const {
    return WritingModule && WritingModule->isModulePurview();
  }

private:
  // ASTDeserializationListener implementation
  void ReaderInitialized(ASTReader *Reader) override;
  void IdentifierRead(serialization::IdentID ID, IdentifierInfo *II) override;
  void MacroRead(serialization::MacroID ID, MacroInfo *MI) override;
  void TypeRead(serialization::TypeIdx Idx, QualType T) override;
  void SelectorRead(serialization::SelectorID ID, Selector Sel) override;
  void MacroDefinitionRead(serialization::PreprocessedEntityID ID,
                           MacroDefinitionRecord *MD) override;
  void ModuleRead(serialization::SubmoduleID ID, Module *Mod) override;

  // ASTMutationListener implementation.
  void CompletedTagDefinition(const TagDecl *D) override;
  void AddedVisibleDecl(const DeclContext *DC, const Decl *D) override;
  void AddedCXXImplicitMember(const CXXRecordDecl *RD, const Decl *D) override;
  void AddedCXXTemplateSpecialization(
      const ClassTemplateDecl *TD,
      const ClassTemplateSpecializationDecl *D) override;
  #if ENABLE_BSC
  void AddedCXXTemplateSpecialization(
      const TraitTemplateDecl *TD,
      const TraitTemplateSpecializationDecl *D) override;
  #endif
  void AddedCXXTemplateSpecialization(
      const VarTemplateDecl *TD,
      const VarTemplateSpecializationDecl *D) override;
  void AddedCXXTemplateSpecialization(const FunctionTemplateDecl *TD,
                                      const FunctionDecl *D) override;
  void ResolvedExceptionSpec(const FunctionDecl *FD) override;
  void DeducedReturnType(const FunctionDecl *FD, QualType ReturnType) override;
  void ResolvedOperatorDelete(const CXXDestructorDecl *DD,
                              const FunctionDecl *Delete,
                              Expr *ThisArg) override;
  void CompletedImplicitDefinition(const FunctionDecl *D) override;
  void InstantiationRequested(const ValueDecl *D) override;
  void VariableDefinitionInstantiated(const VarDecl *D) override;
  void FunctionDefinitionInstantiated(const FunctionDecl *D) override;
  void DefaultArgumentInstantiated(const ParmVarDecl *D) override;
  void DefaultMemberInitializerInstantiated(const FieldDecl *D) override;
  void AddedObjCCategoryToInterface(const ObjCCategoryDecl *CatD,
                                    const ObjCInterfaceDecl *IFD) override;
  void DeclarationMarkedUsed(const Decl *D) override;
  void DeclarationMarkedOpenMPThreadPrivate(const Decl *D) override;
  void DeclarationMarkedOpenMPDeclareTarget(const Decl *D,
                                            const Attr *Attr) override;
  void DeclarationMarkedOpenMPAllocate(const Decl *D, const Attr *A) override;
  void RedefinedHiddenDefinition(const NamedDecl *D, Module *M) override;
  void AddedAttributeToRecord(const Attr *Attr,
                              const RecordDecl *Record) override;
};

/// AST and semantic-analysis consumer that generates a
/// precompiled header from the parsed source code.
class PCHGenerator : public SemaConsumer {
  const Preprocessor &PP;
  std::string OutputFile;
  std::string isysroot;
  Sema *SemaPtr;
  std::shared_ptr<PCHBuffer> Buffer;
  llvm::BitstreamWriter Stream;
  ASTWriter Writer;
  bool AllowASTWithErrors;
  bool ShouldCacheASTInMemory;

protected:
  ASTWriter &getWriter() { return Writer; }
  const ASTWriter &getWriter() const { return Writer; }
  SmallVectorImpl<char> &getPCH() const { return Buffer->Data; }

public:
  PCHGenerator(const Preprocessor &PP, InMemoryModuleCache &ModuleCache,
               StringRef OutputFile, StringRef isysroot,
               std::shared_ptr<PCHBuffer> Buffer,
               ArrayRef<std::shared_ptr<ModuleFileExtension>> Extensions,
               bool AllowASTWithErrors = false, bool IncludeTimestamps = true,
               bool ShouldCacheASTInMemory = false);
  ~PCHGenerator() override;

  void InitializeSema(Sema &S) override { SemaPtr = &S; }
  void HandleTranslationUnit(ASTContext &Ctx) override;
  ASTMutationListener *GetASTMutationListener() override;
  ASTDeserializationListener *GetASTDeserializationListener() override;
  bool hasEmittedPCH() const { return Buffer->IsComplete; }
};

} // namespace clang

#endif // LLVM_CLANG_SERIALIZATION_ASTWRITER_H
