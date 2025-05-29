struct A {
    owned int a;  // expected-error {{unknown type name 'owned'}}
    owned int* b; // expected-error {{unknown type name 'owned'}}
};
