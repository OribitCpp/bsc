set(LLVM_LINK_COMPONENTS
  FrontendOpenMP
  MC
  MCParser
  Support
  )

add_clang_library(clangParse
  BSC/ParseDeclBSC.cpp
  BSC/ParseExprBSC.cpp
  BSC/ParseStmtBSC.cpp
  ParseAST.cpp
  ParseCXXInlineMethods.cpp
  ParseDecl.cpp
  ParseDeclCXX.cpp
  ParseExpr.cpp
  ParseExprCXX.cpp
  ParseHLSL.cpp
  ParseInit.cpp
  ParseObjc.cpp
  ParseOpenMP.cpp
  ParsePragma.cpp
  ParseStmt.cpp
  ParseStmtAsm.cpp
  ParseTemplate.cpp
  ParseTentative.cpp
  Parser.cpp

  LINK_LIBS
  clangAST
  clangBasic
  clangLex
  clangSema

  DEPENDS
  omp_gen
  )
