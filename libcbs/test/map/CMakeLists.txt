add_libcbs_test_suite(libcbs-map-tests)

add_libcbs_test(
  test_map
  SUITE
    libcbs-map-tests
  SRCS
    test_map.cbs
)
