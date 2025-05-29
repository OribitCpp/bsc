clang_tablegen(AttrTemplateInstantiate.inc -gen-clang-attr-template-instantiate ${BSC_OPTION}
  -I ${CMAKE_CURRENT_SOURCE_DIR}/../../
  SOURCE ../Basic/Attr.td
  TARGET ClangAttrTemplateInstantiate)
  
clang_tablegen(AttrParsedAttrList.inc -gen-clang-attr-parsed-attr-list ${BSC_OPTION}
  -I ${CMAKE_CURRENT_SOURCE_DIR}/../../
  SOURCE ../Basic/Attr.td
  TARGET ClangAttrParsedAttrList)

clang_tablegen(AttrParsedAttrKinds.inc -gen-clang-attr-parsed-attr-kinds ${BSC_OPTION}
  -I ${CMAKE_CURRENT_SOURCE_DIR}/../../
  SOURCE ../Basic/Attr.td
  TARGET ClangAttrParsedAttrKinds)

clang_tablegen(AttrSpellingListIndex.inc -gen-clang-attr-spelling-index ${BSC_OPTION}
  -I ${CMAKE_CURRENT_SOURCE_DIR}/../../
  SOURCE ../Basic/Attr.td
  TARGET ClangAttrSpellingListIndex)

clang_tablegen(AttrParsedAttrImpl.inc -gen-clang-attr-parsed-attr-impl ${BSC_OPTION}
  -I ${CMAKE_CURRENT_SOURCE_DIR}/../../
  SOURCE ../Basic/Attr.td
  TARGET ClangAttrParsedAttrImpl)
