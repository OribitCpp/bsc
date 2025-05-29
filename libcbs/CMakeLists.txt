cmake_minimum_required(VERSION 3.13.4)

# Use the prebuilt clang compiler to build libcbs
set(BSC_CLANG "${CMAKE_BINARY_DIR}/bin/clang")
set(LIBCBS_SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(LIBC_TARGET_OS ${CMAKE_SYSTEM_NAME})
string(TOLOWER ${LIBC_TARGET_OS} LIBC_TARGET_OS)

if(NOT BSC_CLANG)
  find_program(BSC_CLANG NAMES clang clang-X.Y)
endif()

set(CMAKE_EXE_LINKER_FLAGS "-lpthread")

set(CMAKE_C_COMPILER ${BSC_CLANG})

string(REPLACE "-fcoverage-mapping" "" CMAKE_C_FLAGS "${CMAKE_C_FLAGS}")
string(REPLACE "-fcoverage-mapping" "" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules")
include(LLVMLibCBSRules)

# Compile the source code, create multiple object files from each folder.
add_subdirectory(src)
add_subdirectory(test)

# TODO: learn from libc
# Pack the object files and create a final library we want to ship.
# add_subdirectory(lib)
