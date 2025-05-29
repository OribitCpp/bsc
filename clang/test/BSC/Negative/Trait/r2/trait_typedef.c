// RUN: %clang %s -o %t.output
// RUN: %t.output
// expected-no-diagnostics

// typedef of trait is ok in C code
typedef int trait;
trait x = 1;

int main() {
  trait y = x;
  return 0;
}
