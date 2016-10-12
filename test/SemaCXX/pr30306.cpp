// RUN: %clang_cc1 -fsyntax-only -verify %s
int f(int const &p) { return p; }

template <typename T>
void g(T) { int a[f(3)]; } // expected-no-diagnostics

int main() {
  g<int>(2);
  return 0;
}
