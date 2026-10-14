// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_init_var_plus_ind2.c
// SV-COMP array-cav19/array_init_var_plus_ind2.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_init_var_plus_ind2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_init_var_plus_ind2.c", 7, "reach_error"); }
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
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  assume_abort_if_not(0 < N);
  int a[N];
  j = 0;
  k = 0;
  i = 0;
  while (i < N) {
    x = __VERIFIER_nondet_int();
    if (x != 0) {
      break;
    }
    a[i] = j;
    j = j + i;
    k = k - i;
    i = i + 1;
  }
  l = 1;
  while (l < i) {
    __VERIFIER_assert(a[l] >= k);
    l = l + 1;
  }
}

