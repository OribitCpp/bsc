add_libcbs_test_suite(libcbs-rc-tests)

add_libcbs_test(
  test_rc_deref
  SUITE
    libcbs-rc-tests
  SRCS
    rc_deref.cbs
)

add_libcbs_test(
  test_rc_or_weak_is_field_in_struct
  SUITE
    libcbs-rc-tests
  SRCS
    rc_or_weak_is_field_in_struct.cbs
)

add_libcbs_test(
  test_ref_count_check
  SUITE
    libcbs-rc-tests
  SRCS
    ref_count_check.cbs
)

add_libcbs_test(
  test_weak_upgrade
  SUITE
    libcbs-rc-tests
  SRCS
    weak_upgrade.cbs
)

add_libcbs_test(
  test_weak_tree
  SUITE
    libcbs-rc-tests
  SRCS
    weak_tree.cbs
)

add_libcbs_test(
  test_weak_circular_reference
  SUITE
    libcbs-rc-tests
  SRCS
    weak_circular_reference.cbs
)