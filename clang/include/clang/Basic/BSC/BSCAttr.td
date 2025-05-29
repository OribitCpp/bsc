def AsyncFunction : SubsetSubject<Function,
                             [{S->isAsyncSpecified()}], "async functions">;

def Count : InheritableParamAttr {
  let Spellings = [GNU<"count">];
  let Subjects = SubjectList<[Function, ParmVar, Field, Var]>;
  let Documentation = [Undocumented];
  let Args = [ExprArgument<"LenExpr">, VariadicParamIdxArgument<"Index">];
  let InheritEvenIfAlreadyPresent = 1;
  let LateParsed = 1;
  let TemplateDependent = 1;
}

def ReturnsCount : InheritableAttr {
  let Spellings = [GNU<"returns_count">];
  let Subjects = SubjectList<[Function, Var, Field]>;
  let Documentation = [Undocumented];
  let Args = [ExprArgument<"LenExpr">];
  let InheritEvenIfAlreadyPresent = 1;
  let LateParsed = 1;
  let TemplateDependent = 1;
}

def CountIndex : InheritableParamAttr {
  let Spellings = [GNU<"count_index">];
  let Subjects = SubjectList<[Function, ParmVar, Field, Var]>;
  let Documentation = [Undocumented];
  let Args = [ParamIdxArgument<"LenVarIndex">, VariadicParamIdxArgument<"Index">];
  let InheritEvenIfAlreadyPresent = 1;
  let TemplateDependent = 1;
}

def ReturnsCountIndex : InheritableAttr {
  let Spellings = [GNU<"returns_count_index">];
  let Subjects = SubjectList<[Function, Field, Var]>;
  let Documentation = [Undocumented];
  let Args = [ParamIdxArgument<"LenVarIndex">];
  let InheritEvenIfAlreadyPresent = 1;
  let TemplateDependent = 1;
}

// byte_count
def ByteCount : InheritableParamAttr {
  let Spellings = [GNU<"byte_count">];
  let Subjects = SubjectList<[Function, ParmVar, Field, Var]>;
  let Documentation = [Undocumented];
  let Args = [ExprArgument<"LenExpr">, VariadicParamIdxArgument<"Index">];
  let InheritEvenIfAlreadyPresent = 1;
  let LateParsed = 1;
  let TemplateDependent = 1;
}

def ReturnsByteCount : InheritableAttr {
  let Spellings = [GNU<"returns_byte_count">];
  let Subjects = SubjectList<[Function, Var, Field]>;
  let Documentation = [Undocumented];
  let Args = [ExprArgument<"LenExpr">];
  let InheritEvenIfAlreadyPresent = 1;
  let LateParsed = 1;
  let TemplateDependent = 1;
}

def ByteCountIndex : InheritableParamAttr {
  let Spellings = [GNU<"byte_count_index">];
  let Subjects = SubjectList<[Function, ParmVar, Field, Var]>;
  let Documentation = [Undocumented];
  let Args = [ParamIdxArgument<"LenVarIndex">, VariadicParamIdxArgument<"Index">];
  let InheritEvenIfAlreadyPresent = 1;
  let TemplateDependent = 1;
}

def ReturnsByteCountIndex : InheritableAttr {
  let Spellings = [GNU<"returns_byte_count_index">];
  let Subjects = SubjectList<[Function, Var, Field]>;
  let Documentation = [Undocumented];
  let Args = [ParamIdxArgument<"LenVarIndex">];
  let InheritEvenIfAlreadyPresent = 1;
  let TemplateDependent = 1;
}

def FunctionLikeMacro : InheritableAttr {
  let Spellings = [GNU<"function_like_macro">];
  let Subjects = SubjectList<[Function]>;
  let Documentation = [Undocumented];
}

def Operator : InheritableAttr {
  let Spellings = [GNU<"operator">];
  let Subjects = SubjectList<[Function]>;
  let Args = [IntArgument<"OperatorKind">];
  let Documentation = [Undocumented];
}
