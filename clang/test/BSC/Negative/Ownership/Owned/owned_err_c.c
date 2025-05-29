// RUN: %clang_cc1 -ast-dump -verify %s

struct A {
    owned int a;  // expected-error {{unknown type name 'owned'}}
    owned int* b; // expected-error {{unknown type name 'owned'}}
};
