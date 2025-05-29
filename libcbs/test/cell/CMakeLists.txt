add_libcbs_test_suite(libcbs-cell-tests)

add_libcbs_test(
  test_cell_for_copy_type
  SUITE
    libcbs-cell-tests
  SRCS
    cell_for_copy_type.cbs
)

add_libcbs_test(
  test_refcell_deref
  SUITE
    libcbs-cell-tests
  SRCS
    refcell_deref.cbs
)

add_libcbs_test(
  test_refcell_try_borrow
  SUITE
    libcbs-cell-tests
  SRCS
    refcell_try_borrow.cbs
)