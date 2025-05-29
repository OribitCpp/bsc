// BSC instance member warnings and errors.
def note_no_this_parameter : Note<"found the following member function %0 which doesn't have a 'this' parameter">;
def err_no_instance_member : Error<
  "no instance member named %0 in %1; did you mean to use '::' instead of '%select{.|->}2'?">;
def err_cvrqualified_member_type_unsupported : Error<
  "type of member function is wrong, CVR qualified type is unsupported, but found '%0'">;
def err_cvrqualified_this_type_unsupported : Error<
  "owned type requires a pointer, '%0' is invalid">;
def err_this_type_unsupported : Error<
  "type of parameter 'this' is wrong, expected 'This*' or 'This' or '%0*' or '%0', but found '%1'">;
def err_incompatible_pointer_cast : Error<
  "incompatible conversion from pointer type '%0' to non-pointer type '%1' in member function call">;
def err_incompatible_const_cast : Error<
  "incompatible conversion from const type '%0' to non-const type '%1' in member function call">;
def err_incompatible_owned_cast : Error<
  "incompatible conversion from non owned type '%0' to owned type '%1' in member function call">;

// BSC attributes warnings and errors.
def warn_attribute_no_pointers : Warning<
  "(EnhanceC) %0 attribute applied to function with no pointer arguments">,
  InGroup<IgnoredAttributes>;
def err_attribute_redundant_pointers : Error<
  "(EnhanceC) %0 attribute applied to function with more than one pointer arguments, "
  "please specify the index argument in the %0 attribute">;
def warn_attribute_function_pointer : Warning<
  "(EnhanceC) %0 attribute applied to function and function type pointer">,
  InGroup<IgnoredAttributes>;
def err_attribute_zero_pointer : Error<
  "(EnhanceC) %0 attribute: The number of pointer arguments index cannot be zero">;

// BSC async/await warnings and errors.
def err_async_non_function : Error<
  "'async' can only appear on functions">;
def err_async_main : Error<"'main' is not allowed to be declared async">;
def err_await_invalid_scope : Error<
  "await expression is not allowed to appear in %0">;
def err_async_func_unsupported : Error<
  "async function does not support %0">;
def err_not_a_async_call : Error<
  "the await expression's external function declaration must be modified by async or return 'Future' type">;
def err_function_not_found : Error <
  "'%0' was not found, you need to include %1 before using the 'async' keyword">;
def err_await_expression_not_found: Error <
  "await expression was not found in async function">;
def err_invalid_async_function : Error <
  "function which returns 'Future' type should not be modified by 'async'">;

// BSC ownership warnings and errors.
def err_owned_inderictOwned_type_check : Error<
  "%select{"
  "type of %2 cannot qualified by '%1' |"
  "type of %2 cannot qualified by '%1', %3 contains '%1' type |"
  "type of %2 cannot qualified by '%1'(even indirectly), %3 contains '%1' type}0">;
def err_owned_decl: Error<"%0 cannot be qualified by 'owned'">;
def err_owned_funcPtr_incompatible : Error<"cannot cast %0 to %1">;
def err_owned_qualcheck_incompatible : Error<
  "incompatible owned types, cannot cast %0 to %1">;
def err_typecheck_invalid_owned_binOp : Error<
  "invalid operands to binary expression (%0 and %1)">;
def err_typecheck_invalid_owned_unaOp : Error<
  "invalid operands to unary expression (%0)">;
def err_typecheck_invalid_owned_arrsub : Error<
  "owned pointer type (%0) do not support ArraySubscript operate">;
def err_owned_temporary_memLeak : Error<
  "memory leak because temporary variable '%0' is owned or indirect owned type, please fix it">;
def err_funcPtr_incompatible : Error<
  "incompatible borrow function pointer types, cannot cast %0 to %1">;
def err_borrow_on_borrow : Error<"%0 on a 'borrow' quialified type is not allowed">;
def err_mut_expr_unmodifiable  : Error<"the expression after '&mut' must be modifiable">;
def err_mut_expr_func : Error<"'&mut' for function pointer is not allowed">;
def err_safe_mut : Error<"global or static variables are not allowed to be mutably borrowed within the safe zone">;
def err_move_borrow : Error<"borrow type does not allow move ownership">;
def err_typecheck_invalid_borrow_not_pointer : Error<"borrow type requires a pointer or reference (%0 is invalid)">;
def err_borrow_qualcheck_incompatible : Error<
  "incompatible borrow types, cannot cast %0 to %1">;
def err_borrow_qualcheck_compare : Error<
  "incompatible borrow types, %0 and %1 cannot be compared">;
def err_typecheck_borrow_func : Error<"no borrow qualified type found in the function parameters, the return type is not allowed to be borrow qualified">;
def err_typecheck_borrow_subscript : Error<"subscript of borrow pointer is not allowed">;
def err_owned_and_borrow_conflict : Error<"cannot combine 'owned' and 'borrow' qualifiers on the same type">;


// BSC trait warnings and errors.
def err_variables_not_trait_pointer : Error<"only trait pointer type is allowed to be declared">;
def err_trait_impl : Error<"function %0 in %1 is not implemented for %2">;
def err_trait_impl_function_type_conflict : Error<
  "type of %0 conflicts with that of %1">;
def err_type_has_not_impl_trait : Error<
  "expected a pointer type which has implemented %0, found %1">;
def err_trait_member_not_func : Error<
  "only function declarations can be trait member">;
def warn_type_has_not_impl_trait : Warning<
  "expected a pointer type which has implemented %0, found %1">,
  InGroup<BSCTraitMissing>;
def err_trait_is_undefined : Error<"%0 must be defined before it can be used">;
def err_impl_trait_for_instantiated_type : Error<
  "cannot impl trait for an instantiated type">;

// BSC generic warnings and errors.
def err_invalid_struct_definition : Error <
  "struct definition in generic fuction is not supported in BSC">;
def err_extended_type_not_instantiated_type : Error<
  "extended type of a BSC member function cannot be an instantiated type">;

// BSC constexpr warnings and errors.
def err_constexpr_func_unsupported : Error<
  "BSC constexpr function does not support %0">;
def err_constexpr_func_unsupported_type : Error<
  "BSC constexpr function does not support type %0">;
def err_constexpr_var_unsupported_type : Error<
  "BSC constexpr variable does not support type %0">;
def err_constexpr_if_cond_expr_unsupported_type : Error<
  "BSC constexpr if condition expression does not support type %0">;

// BSC safe scope warnings and errors.
def err_unsafe_cast : Error<"conversion from type %0 to %1 is forbidden in the safe zone">;
def err_unsafe_fun_cast : Error<"conversion from type %0 to %1 is forbidden">;
def err_safe_function : Error<"%0 is forbidden in the safe function">;
def err_safe_zone_decl : Error<"%select{|'safe'|'unsafe'}0 can only appear before on function or compound statement"> ;
def err_safe_global_var : Error<"defining mutable global variables is not allowed within the safe zone"> ;

// BSC owned struct
def err_invalid_member_use_in_class_method : Error <
  "invalid implicit use of member %0 in struct member function">;
def err_static_class_func : Error<
  "function declared in struct scope cannot have 'static' storage class">;
  def err_need_explicit_constructor_owned_struct : Error<"need explicit constructor because %0 has private field">;
def err_struct_member_redeclared : Error<"struct member cannot be redeclared">;

// BSC Destructor
def invalid_param_for_destructor : Error<"the parameter of destructor must be '%0 this'">;
def invalid_param_num_for_destructor : Error<"destructor can only have one parameter">;
def err_destructor_call : Error<"destructor %0 cannot be called directly">;
def err_assignment_in_destructor : Error<"'this' cannot be moved in destructor">;
def warn_destructor_execute : Warning<"the destructor may be not executed">,
InGroup<BSCOwnedStruct>;
def err_owned_struct_destructor_name : Error<"expected the owned struct name after '~' to name the enclosing owned struct">;
def err_owned_struct_destructor_body : Error<"destructor must have a function body">;

// BSC Ownership Analysis errors.
// use
def err_ownership_use_moved : Error<
  "use of moved value: `%0`">,
  InGroup<UseMovedOwned>;
def err_ownership_use_partially_moved : Error<
  "use of partially moved value: `%0`, %1 moved">,
  InGroup<UseMovedOwned>;
def err_ownership_use_all_moved: Error<
  "use of all moved value: `%0`">,
  InGroup<UseMovedOwned>;
def err_ownership_use_uninit : Error<
  "use of uninitialized value: `%0`">,
  InGroup<UseUninitOwned>;
def err_ownership_use_possibly_uninit : Error<
  "use of possibly uninitialized value: `%0`">,
  InGroup<UseUninitOwned>;

// assign
def err_ownership_assign_owned : Error<
  "assign to owned value: `%0`">,
  InGroup<AssignOwned>;
def err_ownership_assign_partially_moved : Error<
  "assign to partially moved value: `%0`, %1 moved">,
  InGroup<AssignMovedOwned>;
def err_ownership_assign_possibly_partially_moved : Error<
  "assign to possibly partially moved value: `%0`, %1 possibly moved">,
  InGroup<AssignMovedOwned>;
def err_ownership_assign_all_moved : Error<
  "assign to all moved value: `%0`">,
  InGroup<AssignMovedOwned>;
// field assign
def err_ownership_assign_field_uninit : Error<
  "assign to part of uninitialized value: `%0`">,
  InGroup<AssignUninitOwned>;
def err_ownership_assign_field_owned : Error<
  "assign to part of owned value: `%0`">,
  InGroup<AssignOwned>;
def err_ownership_assign_field_moved : Error<
  "assign to part of moved value: `%0`">,
  InGroup<AssignMovedOwned>;
def err_ownership_assign_field_subfield_owned : Error<
  "assign to subfield owned value: `%0`, %1 owned">,
  InGroup<AssignOwned>;

// cast to `void * owned`
def err_ownership_cast_moved : Error<
  "invalid cast to `void * owned` of moved value: `%0`">,
  InGroup<CastMovedOwned>;
def err_ownership_cast_owned : Error<
  "invalid cast to `void * owned` of owned value: `%0`">,
  InGroup<CastOwned>;
def err_ownership_cast_uninit: Error<
  "invalid cast to `void * owned` of uninit value: `%0`">,
  InGroup<CastOwned>;
def err_ownership_cast_subfield_owned : Error<
  "invalid cast to `void * owned` of not all moved value: `%0`, %1 owned">,
  InGroup<CastOwned>;
// memory leak
def err_ownership_memory_leak_field : Error<
  "field memory leak of value: `%0`, %1 leak">,
  InGroup<CheckMemoryLeak>;
def err_ownership_memory_leak : Error<
  "memory leak of value: `%0`">,
  InGroup<CheckMemoryLeak>;

// BSC Borrow Checker errors.
def err_borrow_live_longer_than_target_var : Error<
  "borrow pointer variable '%0' lives longer than target variable">;
def err_at_most_one_mut_borrow : Error<
  "There should be at most one mutable borrow targeting to '%0' at the same time">;
def err_return_value_borrow_local : Error<
  "Return value cannot be a borrow from local variable '%0'">;
def err_modify_after_be_borrow : Error<
  "Can not modify '%0' because be borrowed">;
def err_read_after_be_mut_borrow : Error<
  "Can not read '%0' because be mut borrowed">;
def note_previous_borrow : Note<"previous borrow is here">;
def err_use_expired_borrow_var : Error<
  "Can not use '%0' because expired">;

// New BSC Borrow Checker errors.
def err_borrow_assign_when_borrowed : Error<
  "cannot assign to `%0` because it is borrowed">,
  InGroup<AssignBorrowed>;
def err_borrow_move_when_borrowed : Error<
  "cannot move out of `%0` because it is borrowed">,
  InGroup<MoveBorrowed>;
def err_borrow_use_when_mut_borrowed : Error<
  "cannot use `%0` because it was mutably borrowed">,
  InGroup<UseMutablyBorrowed>;
def note_borrowed_here : Note<"`%0` is borrowed here">;
def err_borrow_mut_borrow_more_than_once : Error<
  "cannot borrow `%0` as mutable more than once at a time">,
  InGroup<RepeatedBorrow>;
def note_first_mut_borrow_occurs_here : Note<"first mut borrow occurs here">;
def err_borrow_return_local_borrow : Error<
  "cannot return reference to local variable `%0`">,
  InGroup<ReturnLocalBorrow>;
def err_borrow_not_live_long : Error<
  "`%0` does not live long enough">,
  InGroup<ShortLifeBorrow>;
def note_dropped_while_borrowed: Note<"`%0` dropped here while still borrowed">;
def err_borrow_immut_borrow_when_mut_borrowed : Error<
  "cannot borrow `%0` as immutable because it is also borrowed as mutable">,
  InGroup<RepeatedBorrow>;
def note_mutable_borrow_occurs_here : Note<"mutable borrow occurs here">;
def err_borrow_mut_borrow_when_immut_borrowed : Error<
  "cannot borrow `%0` as mutable because it is also borrowed as immutable">,
  InGroup<RepeatedBorrow>;
def note_immutable_borrow_occurs_here : Note<"immutable borrow occurs here">;

// BSC operator overload errors.
def err_unsupport_overload_fun : Error<"function unsupport overload">;
def err_operator_overload_needs_point : Error<
  "overloaded function %0 first parameter or return type must be struct or enumeration pointer type">;

// BSC Pointer Nullability Check errors.
def err_nullable_pointer_dereference : Error<
  "nullable pointer cannot be dereferenced">,
  InGroup<DerefNullable>;
def err_pass_nullable_argument : Error<
  "cannot pass nullable pointer argument">,
  InGroup<PassNullable>;
def err_return_nullable : Error<
  "cannot return nullable pointer type">,
  InGroup<ReturnNullable>;
def err_nullable_cast_nonnull : Error<
  "cannot cast nullable pointer to nonnull type">,
  InGroup<CastNullable>;
def err_nullable_pointer_access_member : Error<
  "cannot access member through nullable pointer">,
  InGroup<AssignNullable>;
def err_nonnull_assigned_by_nullable : Error<
  "nonnull pointer cannot be assigned by nullable pointer">,
  InGroup<AssignNonnull>;

