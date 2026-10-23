// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-industry-pattern/array_of_struct_single_elem_init.c
// SV-COMP array-industry-pattern/array_of_struct_single_elem_init.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_of_struct_single_elem_init.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_of_struct_single_elem_init.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int n[N], p[N];
  assume_abort_if_not(3 < N);
  i = 0;
  while (i < N) {
    q = __VERIFIER_nondet_int();
    x = __VERIFIER_nondet_int();
    if (x == 0) {
      p[i] = 10;
    } else {
      p[i] = 20;
    }
    n[i] = x;
    i = i + 1;
  }
  p[3] = 30;
  n[3] = 40;
  i = 0;
  while (i < N) {
    if (i != 3 && n[i] == 0) {
      __VERIFIER_assert(p[i] == 10);
    }
    i = i + 1;
  }
}

