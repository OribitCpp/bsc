add_libcbs_test_suite(libcbs-safety-tests)

add_libcbs_test(
  test_safety
  SUITE
    libcbs-safety-tests
  SRCS
    bishengc_safety_test.cbs
)
