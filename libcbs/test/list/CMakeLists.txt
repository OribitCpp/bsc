add_libcbs_test_suite(libcbs-list-tests)

add_libcbs_test(
  test_list
  SUITE
    libcbs-list-tests
  SRCS
    test_list.cbs
)

add_libcbs_test(
  list_list
  SUITE
    libcbs-list-tests
  SRCS
    list_list.cbs
)
