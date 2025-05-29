# Rule to add an integration test. An integration test is like a unit test
# Usage:
#   add_libcbs_test(
#     <target name>
#     SUITE <the suite to which the test should belong>
#     SRCS <src1.cpp> [src2.cpp ...]
#     HDRS [hdr1.cpp ...]
#     DEPENDS <list of entrypoint or other object targets>
#     ARGS <list of command line arguments to be passed to the test>
#     ENV <list of environment variables to set before running the test>
#   )
function(add_libcbs_test test_name)
  get_fq_target_name(${test_name} fq_target_name)
  if(NOT (${LIBC_TARGET_OS} STREQUAL "linux"))
    message(STATUS "Skipping ${fq_target_name} as it is not available on ${LIBC_TARGET_OS}.")
    return()
  endif()
  cmake_parse_arguments(
    "INTEGRATION_TEST"
    "" # No optional arguments
    "SUITE" # Single value arguments
    "SRCS;HDRS;DEPENDS;ARGS;ENV" # Multi-value arguments
    ${ARGN}
  )

  if(NOT INTEGRATION_TEST_SUITE)
    message(FATAL_ERROR "SUITE not specified for ${fq_target_name}")
  endif()

  if(NOT INTEGRATION_TEST_SRCS)
    message(FATAL_ERROR "The SRCS list for add_integration_test is missing.")
  endif()

  add_executable(
    ${fq_target_name}
    EXCLUDE_FROM_ALL
    ${INTEGRATION_TEST_SRCS}
    ${INTEGRATION_TEST_HDRS}
  )

  set_target_properties(${fq_target_name}
      PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})

  target_link_options(${fq_target_name} PRIVATE -L${CMAKE_BINARY_DIR}/lib/)
  target_link_libraries(${fq_target_name} stdcbs)

  add_custom_command(
    TARGET ${fq_target_name}
    POST_BUILD
    COMMAND ${INTEGRATION_TEST_ENV} $<TARGET_FILE:${fq_target_name}> ${INTEGRATION_TEST_ARGS}
  )

  add_dependencies(${INTEGRATION_TEST_SUITE} ${fq_target_name})
endfunction(add_libcbs_test)
