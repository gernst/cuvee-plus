// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/array_ptr_single_elem_init-2.c
// SV-COMP array-industry-pattern/array_ptr_single_elem_init-2.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_ptr_single_elem_init-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_ptr_single_elem_init-2.c", 7, "reach_error"); }
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
  int N = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 134217727);
  int a[N];
  int b[N];
  int c[N];
  assume_abort_if_not(0 < N);
  i = 0;
  while (i < N) {
    q = __VERIFIER_nondet_int();
    a[i] = 0;
    if (q == 0) {
      a[i] = 1;
      b[i] = i % 2;
    }
    if (a[i] != 0) {
      if (b[i] == 0) {
        c[i] = 0;
      } else {
        c[i] = 1;
      }
    }
    i = i + 1;
  }
  a[15000] = 1;
  i = 0;
  while (i < N) {
    if (i == 15000) {
      __VERIFIER_assert(a[i] != 1);
    }
    i = i + 1;
  }
}

