// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sanfoundry_24-1.c
// SV-COMP array-examples/sanfoundry_24-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/sanfoundry_24-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sanfoundry_24-1.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int i = __VERIFIER_nondet_int();
  int num = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  num = __VERIFIER_nondet_int();
  i = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && num <= N && N <= 536870911);
  int Array[N];
  while (i < num) {
    v = __VERIFIER_nondet_int();
    Array[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < num) {
    if (Array[i] % 2 == 0) {
      __VERIFIER_assert(Array[i] % 2 == 0);
    }
    i = i + 1;
  }
  i = 0;
  while (i < num) {
    if (Array[i] % 2 != 0) {
      __VERIFIER_assert(Array[i] % 2 != 0);
    }
    i = i + 1;
  }
}

