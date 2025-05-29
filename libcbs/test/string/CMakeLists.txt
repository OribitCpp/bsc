add_libcbs_test_suite(libcbs-string-tests)

add_libcbs_test(
  test_string
  SUITE
    libcbs-string-tests
  SRCS
    string_test.cbs
)
