add_libcbs_test_suite(libcbs-scheduler-tests)

add_libcbs_test(
  test_scheduler
  SUITE
    libcbs-scheduler-tests
  SRCS
    scheduler_test.cbs
)
