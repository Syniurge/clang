// RUN: %clang_cc1 %s -emit-llvm -triple %itanium_abi_triple -std=c++11 -o - | FileCheck %s
// RUN: %clang_cc1 %s -emit-llvm -triple i686-linux-gnu -std=c++11 -o - | FileCheck %s
// RUN: %clang_cc1 %s -emit-llvm -triple x86_64-linux-gnu -std=c++11 -o - | FileCheck %s

struct __attribute__((abi_tag("A", "B"))) A { };

struct B: A { };

template<class T>

struct C {
};

struct D { A* p; };

template<class T>
struct __attribute__((abi_tag("C", "D"))) E {
};

struct __attribute__((abi_tag("A", "B"))) F { };

A a1;
// CHECK: @_Z2a1B1AB1B =

__attribute__((abi_tag("C", "D")))
A a2;
// CHECK: @_Z2a2B1AB1BB1CB1D =

B a3;
// CHECK: @a3 =

C<A> a4;
// CHECK: @_Z2a4B1AB1B =

D a5;
// CHECK: @a5 =

E<int> a6;
// CHECK: @_Z2a6B1CB1D =

E<A> a7;
// CHECK: @_Z2a7B1AB1BB1CB1D =

template<>
struct E<float> {
  static float a8;
};
float E<float>::a8;
// CHECK: @_ZN1EB1CB1DIfE2a8E =

template<>
struct E<F> {
  static bool a9;
};
bool E<F>::a9;
// CHECK: @_ZN1EB1CB1DI1FB1AB1BE2a9E =

struct __attribute__((abi_tag("A", "B"))) A10 {
  virtual ~A10() {}
} a10;
// vtable
// CHECK: @_ZTV3A10B1AB1B =
// typeinfo
// CHECK: @_ZTI3A10B1AB1B =

// Local variables from f13.
// f13()::L::foo[abi:C][abi:D]()::a[abi:A][abi:B]
// CHECK-DAG: @_ZZZ3f13vEN1L3fooB1CB1DEvE1aB1AB1B =
// guard variable for f13()::L::foo[abi:C][abi:D]()::a[abi:A][abi:B]
// CHECK-DAG: @_ZGVZZ3f13vEN1L3fooB1CB1DEvE1aB1AB1B =

__attribute__ ((abi_tag("C", "D")))
void* f1() {
  return 0;
}
// CHECK: define {{.*}} @_Z2f1B1CB1Dv(

__attribute__ ((abi_tag("C", "D")))
A* f2() {
  return 0;
}
// CHECK: define {{.*}} @_Z2f2B1AB1BB1CB1Dv(

B* f3() {
  return 0;
}
// CHECK: define {{.*}} @_Z2f3v(

C<A>* f4() {
  return 0;
}
// CHECK: define {{.*}} @_Z2f4B1AB1Bv(

D* f5() {
  return 0;
}
// CHECK: define {{.*}} @_Z2f5v(

E<char>* f6() {
  return 0;
}
// CHECK: define {{.*}} @_Z2f6B1CB1Dv(

E<A>* f7() {
  return 0;
}
// CHECK: define {{.*}} @_Z2f7B1AB1BB1CB1Dv(

void f8(E<A>*) {
}
// CHECK: define {{.*}} @_Z2f8P1EB1CB1DI1AB1AB1BE(

inline namespace Names1 __attribute__((__abi_tag__)) {
    class C1 {};
}
C1 f9() { return C1(); }
// CHECK: @_Z2f9B6Names1v(

inline namespace Names2 __attribute__((__abi_tag__("Tag1", "Tag2"))) {
    class C2 {};
}
C2 f10() { return C2(); }
// CHECK: @_Z3f10B4Tag1B4Tag2v(

void __attribute__((abi_tag("A"))) f11(A) {}
// f11[abi:A](A[abi:A][abi:B])
// CHECK: define {{.*}} @_Z3f11B1A1AB1AB1B(

A f12(A) { return A(); }
// f12(A[abi:A][abi:B])
// CHECK: define {{.*}} @_Z3f121AB1AB1B(

inline void f13() {
  struct L {
    static E<int>* foo() {
      static A10 a;
      return 0;
    }
  };
  L::foo();
}
void f11_test() {
  f13();
}
// f13()::L::foo[abi:C][abi:D]()
// CHECK: define linkonce_odr %struct.E* @_ZZ3f13vEN1L3fooB1CB1DEv(
