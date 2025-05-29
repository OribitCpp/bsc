def BSCTraitMissing : DiagGroup<"bsc-trait-missing">;
def BSCOwnedStruct : DiagGroup<"bsc-owned-struct">;

def DerefNullable : DiagGroup<"deref-nullable">;
def PassNullable : DiagGroup<"pass-nullable">;
def ReturnNullable : DiagGroup<"return-nullable">;
def CastNullable : DiagGroup<"cast-nullable">;
def AssignNullable : DiagGroup<"assign-nullable">;
def AssignNonnull : DiagGroup<"assign-nonnull">;
def BSCNullability : DiagGroup<"bsc-nullability",
                                   [DerefNullable,
                                    PassNullable,
                                    ReturnNullable,
                                    CastNullable,
                                    AssignNullable,
                                    AssignNonnull]>;

def UseMovedOwned : DiagGroup<"use-moved-owned">;
def UseUninitOwned : DiagGroup<"use-uninit-owned">;
def UseOwned : DiagGroup<"use-owned",[UseMovedOwned, UseUninitOwned]>;
def AssignMovedOwned : DiagGroup<"assign-moved-owned">;
def AssignUninitOwned : DiagGroup<"assign-uninit-owned">;
def AssignOwned :  DiagGroup<"assign-owned",[AssignUninitOwned, AssignMovedOwned]>;
def CastMovedOwned : DiagGroup<"cast-moved-owned">;
def CastOwned : DiagGroup<"cast-owned", [CastMovedOwned]>;
def CheckMemoryLeak : DiagGroup<"check-memory-leak">;
def BSCOwnership : DiagGroup<"bsc-ownership", 
                                [UseOwned,
                                 AssignOwned,
                                 CastOwned,
                                 CheckMemoryLeak]>;

def AssignBorrowed : DiagGroup<"assign-borrowed">;
def MoveBorrowed : DiagGroup<"move-borrowed">;
def UseMutablyBorrowed : DiagGroup<"use-mutably-borrowed">;
def RepeatedBorrow : DiagGroup<"repeated-borrow">;
def ReturnLocalBorrow : DiagGroup<"return-local-borrow">;
def ShortLifeBorrow : DiagGroup<"short-life-borrow">;
def BSCBorrow : DiagGroup<"bsc-borrow", 
                                [AssignBorrowed,
                                 MoveBorrowed,
                                 UseMutablyBorrowed,
                                 RepeatedBorrow,
                                 ReturnLocalBorrow,
                                 ShortLifeBorrow]>;

def BSCSafetyCheck : DiagGroup<"bsc-safety-check",
                                [BSCNullability,
                                 BSCOwnership,
                                 BSCBorrow]>;