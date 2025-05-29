set(LLVM_LINK_COMPONENTS
  support
  FrontendOpenMP
  )

add_clang_library(clangTidyBscModule
  
  AccessSpecificTypeCheck.cpp
  AddNewFieldCheck.cpp
  BSCTidyModule.cpp
  ExplicitCastCheck.cpp
  
  LINK_LIBS
  clangTidy
  clangTidyUtils

  DEPENDS
  omp_gen
  )

clang_target_link_libraries(clangTidyBscModule
  PRIVATE
  clangAST
  clangASTMatchers
  clangBasic
  clangLex
  )
