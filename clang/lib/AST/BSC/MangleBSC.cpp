//===--- MangleBSC.cpp - Mangle BSC Names --------------------------*- cbs -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Implements generic name mangling support for bsc.
//
//===----------------------------------------------------------------------===//

#if ENABLE_BSC

#include "clang/AST/BSC/MangleBSC.h"


using namespace clang;

bool MangleBSCContext::mangleBSCName(const NamedDecl *ND, raw_ostream &Out) {
  const auto *BMD = dyn_cast<BSCMethodDecl>(ND);
  const auto *BFD = dyn_cast<FunctionDecl>(ND);
  if (!ManglePolicy.RewriteBSC) {
    ManglePolicy.adjustForRewritingBSC();
  }
  std::string MethodStr;

  if (BMD) {
    // Handle the BSC method, including the name of the type template.
    MethodStr = getBSCMethodMangleName(BMD);
    if (BMD->isTemplateInstantiation()) {
      if (const TemplateArgumentList *TArgs =
              BFD->getTemplateSpecializationArgs()) {
        ArrayRef<TemplateArgument> Args = TArgs->asArray();
        std::string TemplateArgsName =
            getBSCTemplateArgsName(Args, ManglePolicy);
        MethodStr += TemplateArgsName;
      }
    }
  } else if (BFD && BFD->isTemplateInstantiation()) {
    // Handle the functiondecl with template args.
    MethodStr = getBSCFunctionMangleName(BFD, ManglePolicy);
  } else {
    // Without the BSC mangling, handle it separately at the point of call-in.
    return false;
  }
  Out << MethodStr;
  return true;
}

std::string
MangleBSCContext::getBSCMethodMangleName(const BSCMethodDecl *BMD) {
  std::string TypeStr;
  // For destructors, especially the automatically generated destructors, there
  // is no ExtendedType, and handle separately.
  if (BMD->isDestructor()) {
    TypeStr = getBSCDesturctorMangleName(BMD);
  } else {
    QualType T = BMD->getExtendedType();
    TypeStr = getBSCTypeName(T, ManglePolicy)+ "_" + BMD->getNameAsString();
  }
  return TypeStr;
}

std::string
MangleBSCContext::getBSCDesturctorMangleName(const BSCMethodDecl *BMD) {
  QualType BDT =
      Context.getTypeDeclType(dyn_cast<RecordDecl>(BMD->getParent()));
  std::string TypeStr = getBSCTypeName(BDT, ManglePolicy);
  TypeStr += "_D";
  return TypeStr;
}

std::string MangleBSCContext::getBSCFunctionMangleName(const FunctionDecl *BFD,
                                                       PrintingPolicy &Policy) {
  std::string FunctionName = BFD->getNameAsString();
  if (const TemplateArgumentList *TArgs =
          BFD->getTemplateSpecializationArgs()) {
    ArrayRef<TemplateArgument> Args = TArgs->asArray();
    std::string TemplateArgsName = getBSCTemplateArgsName(Args, Policy);
    FunctionName += TemplateArgsName;
  }
  return FunctionName;
}

std::string MangleBSCContext::getBSCTypeName(QualType QT,
                                             PrintingPolicy &Policy) {
  std::string ExtendedTypeStr;
  llvm::raw_string_ostream OS(ExtendedTypeStr);
  QT.print(OS, Policy);
  int len = ExtendedTypeStr.length() - 1;
  for (int i = len; i >= 0; i--) {
    if (ExtendedTypeStr[i] == ' ') {
      if (i == 0) {
        ExtendedTypeStr.replace(i, 1, "");
        continue;
      }
      ExtendedTypeStr.replace(i, 1, "_");
    } else if (ExtendedTypeStr[i] == '*') {
      // Since '*' is not allowed to appear in identifier,
      // we replace it with 'P'.
      // FIXME: it may conflict with user defined type Char_P.
      ExtendedTypeStr.replace(i, 1, "P");
    } else if (ExtendedTypeStr[i] == '(') {
      // Since '(' is not allowed to appear in identifier,
      // we replace it with 'LP'.
      ExtendedTypeStr.replace(i, 1, "LP");
    } else if (ExtendedTypeStr[i] == ')') {
      // Since ')' is not allowed to appear in identifier,
      // we replace it with 'RP'.
      ExtendedTypeStr.replace(i, 1, "RP");
    } else if (ExtendedTypeStr[i] == '[') {
      // Since '[' is not allowed to appear in identifier,
      // we replace it with 'LB'.
      ExtendedTypeStr.replace(i, 1, "LB");
    } else if (ExtendedTypeStr[i] == ']') {
      // Since ']' is not allowed to appear in identifier,
      // we replace it with 'RB'.
      ExtendedTypeStr.replace(i, 1, "RB");
    } else if (ExtendedTypeStr[i] == ',') {
      // Since ',' is not allowed to appear in identifier,
      // we replace it with 'COMMA'.
      ExtendedTypeStr.replace(i, 1, "COMMA");
    }
  }
  return ExtendedTypeStr;
}

std::string
MangleBSCContext::getBSCTemplateArgsName(ArrayRef<TemplateArgument> Args,
                                         PrintingPolicy &Policy) {
  std::string ArgsName = "";
  for (size_t i = 0; i < Args.size(); i++) {
    ArgsName = ArgsName + "_" + getBSCArgName(Args[i], Policy);
  }
  return ArgsName;
}

std::string MangleBSCContext::getBSCArgName(const TemplateArgument &TemplateArg,
                                            PrintingPolicy &Policy) {
  std::string ArgName;
  if (TemplateArg.getKind() == clang::TemplateArgument::ArgKind::Type)
    ArgName = getBSCTypeName(TemplateArg.getAsType(), Policy);
  else if (TemplateArg.getKind() ==
           clang::TemplateArgument::ArgKind::Integral) {
    llvm::APSInt TemplateInt = TemplateArg.getAsIntegral();
    if (TemplateInt.isNegative())
      ArgName = "n" + std::to_string(-TemplateInt.getExtValue());
    else
      ArgName = std::to_string(TemplateInt.getExtValue());
  }
  return ArgName;
}

#endif

