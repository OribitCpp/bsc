set(LLVM_TARGET_DEFINITIONS Options.td)
tablegen(LLVM Options.inc -gen-opt-parser-defs ${BSC_OPTION})
add_public_tablegen_target(ClangDriverOptions)
