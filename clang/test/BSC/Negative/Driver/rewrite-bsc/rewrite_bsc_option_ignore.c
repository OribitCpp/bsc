// RUN: %clang -rewrite-bsc %s 2>&1 | FileCheck %s
// CHECK: warning: ignoring '-rewrite-bsc' option because rewriting input type 'c' is not supported [-Woption-ignored]

int main() { return 0; }