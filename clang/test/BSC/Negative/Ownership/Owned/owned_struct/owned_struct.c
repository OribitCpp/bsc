// RUN: %clang_cc1 -ast-dump -verify %s

#include "owned_struct_c.h"

int main() {
    struct A a;
    return 0;
}
