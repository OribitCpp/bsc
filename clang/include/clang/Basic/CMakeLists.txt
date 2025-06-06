macro(clang_diag_gen component)
  clang_tablegen(Diagnostic${component}Kinds.inc
    -gen-clang-diags-defs -clang-component=${component} ${BSC_OPTION}
    SOURCE Diagnostic.td
    TARGET ClangDiagnostic${component})
endmacro(clang_diag_gen)

clang_diag_gen(Analysis)
clang_diag_gen(AST)
clang_diag_gen(Comment)
clang_diag_gen(Common)
clang_diag_gen(CrossTU)
clang_diag_gen(Driver)
clang_diag_gen(Frontend)
clang_diag_gen(Lex)
clang_diag_gen(Parse)
clang_diag_gen(Refactoring)
clang_diag_gen(Sema)
clang_diag_gen(Serialization)
clang_tablegen(DiagnosticGroups.inc -gen-clang-diag-groups ${BSC_OPTION}
  SOURCE Diagnostic.td
  TARGET ClangDiagnosticGroups)

clang_tablegen(DiagnosticIndexName.inc -gen-clang-diags-index-name ${BSC_OPTION}
  SOURCE Diagnostic.td
  TARGET ClangDiagnosticIndexName)

clang_tablegen(AttrList.inc -gen-clang-attr-list ${BSC_OPTION}
  -I ${CMAKE_CURRENT_SOURCE_DIR}/../../
  SOURCE Attr.td
  TARGET ClangAttrList)

clang_tablegen(AttrSubMatchRulesList.inc -gen-clang-attr-subject-match-rule-list ${BSC_OPTION}
  -I ${CMAKE_CURRENT_SOURCE_DIR}/../../
  SOURCE Attr.td
  TARGET ClangAttrSubjectMatchRuleList)

clang_tablegen(AttrHasAttributeImpl.inc -gen-clang-attr-has-attribute-impl ${BSC_OPTION}
  -I ${CMAKE_CURRENT_SOURCE_DIR}/../../
  SOURCE Attr.td
  TARGET ClangAttrHasAttributeImpl
  )

# ARM NEON and MVE
clang_tablegen(arm_neon.inc -gen-arm-neon-sema
  SOURCE arm_neon.td
  TARGET ClangARMNeon)
clang_tablegen(arm_fp16.inc -gen-arm-neon-sema
  SOURCE arm_fp16.td
  TARGET ClangARMFP16)
clang_tablegen(arm_mve_builtins.inc -gen-arm-mve-builtin-def
  SOURCE arm_mve.td
  TARGET ClangARMMveBuiltinsDef)
clang_tablegen(arm_mve_builtin_cg.inc -gen-arm-mve-builtin-codegen
  SOURCE arm_mve.td
  TARGET ClangARMMveBuiltinCG)
clang_tablegen(arm_mve_builtin_sema.inc -gen-arm-mve-builtin-sema
  SOURCE arm_mve.td
  TARGET ClangARMMveBuiltinSema)
clang_tablegen(arm_mve_builtin_aliases.inc -gen-arm-mve-builtin-aliases
  SOURCE arm_mve.td
  TARGET ClangARMMveBuiltinAliases)
clang_tablegen(arm_sve_builtins.inc -gen-arm-sve-builtins
  SOURCE arm_sve.td
  TARGET ClangARMSveBuiltins)
clang_tablegen(arm_sve_builtin_cg.inc -gen-arm-sve-builtin-codegen
  SOURCE arm_sve.td
  TARGET ClangARMSveBuiltinCG)
clang_tablegen(arm_sve_typeflags.inc -gen-arm-sve-typeflags
  SOURCE arm_sve.td
  TARGET ClangARMSveTypeFlags)
clang_tablegen(arm_sve_sema_rangechecks.inc -gen-arm-sve-sema-rangechecks
  SOURCE arm_sve.td
  TARGET ClangARMSveSemaRangeChecks)
clang_tablegen(arm_cde_builtins.inc -gen-arm-cde-builtin-def
  SOURCE arm_cde.td
  TARGET ClangARMCdeBuiltinsDef)
clang_tablegen(arm_cde_builtin_cg.inc -gen-arm-cde-builtin-codegen
  SOURCE arm_cde.td
  TARGET ClangARMCdeBuiltinCG)
clang_tablegen(arm_cde_builtin_sema.inc -gen-arm-cde-builtin-sema
  SOURCE arm_cde.td
  TARGET ClangARMCdeBuiltinSema)
clang_tablegen(arm_cde_builtin_aliases.inc -gen-arm-cde-builtin-aliases
  SOURCE arm_cde.td
  TARGET ClangARMCdeBuiltinAliases)
clang_tablegen(riscv_vector_builtins.inc -gen-riscv-vector-builtins
  SOURCE riscv_vector.td
  TARGET ClangRISCVVectorBuiltins)
clang_tablegen(riscv_vector_builtin_cg.inc -gen-riscv-vector-builtin-codegen
  SOURCE riscv_vector.td
  TARGET ClangRISCVVectorBuiltinCG)
clang_tablegen(riscv_vector_builtin_sema.inc -gen-riscv-vector-builtin-sema
  SOURCE riscv_vector.td
  TARGET ClangRISCVVectorBuiltinSema)
