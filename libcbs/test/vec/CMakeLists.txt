add_libcbs_test_suite(libcbs-vec-tests)

add_libcbs_test(
  test_vec
  SUITE
    libcbs-vec-tests
  SRCS
    vec_test.cbs
)
