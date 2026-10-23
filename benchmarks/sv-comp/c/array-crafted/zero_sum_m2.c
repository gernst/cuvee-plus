// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-crafted/zero_sum_m2.c
// SV-COMP array-crafted/zero_sum_m2.yml, translated from benchmarks/sv-comp/dafny/array-crafted/zero_sum_m2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "zero_sum_m2.c", 7, "reach_error"); }
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
  int SIZE = __VERIFIER_nondet_int();
  int sum = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int tmp = __VERIFIER_nondet_int();
  SIZE = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && SIZE <= N && N <= 536870911);
  int a[N];
  if (SIZE > 1) {
    sum = 0;
    i = 0;
    while (i < SIZE) {
      tmp = __VERIFIER_nondet_int();
      a[i] = tmp;
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      sum = sum + a[i];
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      sum = sum + a[i];
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      sum = sum - a[i];
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      sum = sum - a[i];
      i = i + 1;
    }
    __VERIFIER_assert(sum == 0);
  }
}

