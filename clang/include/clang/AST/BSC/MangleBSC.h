//===--- MangleBSC.cpp - Mangle BSC Names --------------------------*- cbs -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Defines generic name mangling support for BSC.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_MANGLEBSC_H
#define LLVM_CLANG_AST_MANGLEBSC_H

#if ENABLE_BSC

#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Type.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/AST/BSC/DeclBSC.h"
#include "clang/AST/DeclTemplate.h"

namespace clang {

class MangleBSCContext {
public:
  const ASTContext &Context;
  PrintingPolicy ManglePolicy;

  explicit MangleBSCContext(const ASTContext &Context, PrintingPolicy Policy)
      : Context(Context), ManglePolicy(Policy){};

  bool mangleBSCName(const NamedDecl *ND, raw_ostream &Out);

  static std::string getBSCTypeName(QualType QT, PrintingPolicy &Policy);
  static std::string getBSCTemplateArgsName(ArrayRef<TemplateArgument> Args,
                                            PrintingPolicy &Policy);
  static std::string getBSCFunctionMangleName(const FunctionDecl *BFD,
                                              PrintingPolicy &Policy);

private:
  std::string getBSCMethodMangleName(const BSCMethodDecl *BMD);
  std::string getBSCDesturctorMangleName(const BSCMethodDecl *BMD);

  static std::string getBSCArgName(const TemplateArgument &TemplateArg,
                            PrintingPolicy &Policy);
};
} // namespace clang
#endif
#endif