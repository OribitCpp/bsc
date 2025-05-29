libcbs: BiShengC Language Standard Library

## libcbs vs libc

This directory contains source code for libcbs. libcbs is the standard library for BiShengC Language, whose API is memory safe.
And the implementation of those APIs may have unsafe code, and depend on libc's APIs.

```
 ---------  
  app code
 ---------  memory safe APIs
  libcbs
 ---------  unsafe interface to call libc
   libc
```

## build and install

TODO: make it work with CMake System in LLVM.

## Design

TODO: vec, string, list, map, ...
