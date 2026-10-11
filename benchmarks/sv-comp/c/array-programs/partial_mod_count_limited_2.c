// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-programs/partial_mod_count_limited_2.c
// SV-COMP array-programs/partial_mod_count_limited_2.yml, translated from benchmarks/sv-comp/dafny/array-programs/partial_mod_count_limited_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "partial_mod_count_limited_2.c", 7, "reach_error"); }
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

int N;

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int lim = __VERIFIER_nondet_int();
  int R = __VERIFIER_nondet_int();
  N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int a[N];
  assume_abort_if_not(0 < N && N % 4 == 0);
  j = 0;
  k = 0;
  tmp_1 = __VERIFIER_nondet_int();
  lim = tmp_1;
  R = 2;
  assume_abort_if_not(0 < lim && lim < N / R);
  i = 0;
  while (i < N) {
    a[i] = i + 1;
    if (i > N / 2 && k < lim) {
      a[i] = i % R;
    }
    if (a[i] == 0) {
      k = k + 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 0) {
      j = j + 1;
    }
    __VERIFIER_assert(j < N / (2 * R));
    i = i + 1;
  }
  result = 0;
  return result;
}

