// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/heapsort.c
// SV-COMP loop-invgen/heapsort.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/heapsort.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "heapsort.c", 7, "reach_error"); }
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

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  int r = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(n <= 1073741823);
  if (!(1 <= n)) {
    result = 0;
    return result;
  }
  l = n / 2 + 1;
  r = n;
  if (l > 1) {
    l = l - 1;
  } else {
    r = r - 1;
  }
  while (r > 1) {
    i = l;
    j = 2 * l;
    while (j <= r) {
      if (j < r) {
        __VERIFIER_assert(1 <= j);
        __VERIFIER_assert(j <= n);
        __VERIFIER_assert(1 <= j + 1);
        __VERIFIER_assert(j + 1 <= n);
        tmp_1 = __VERIFIER_nondet_int();
        if (tmp_1 != 0) {
          j = j + 1;
        }
      }
      __VERIFIER_assert(1 <= j);
      __VERIFIER_assert(j <= n);
      tmp_2 = __VERIFIER_nondet_int();
      if (tmp_2 != 0) {
        break;
      }
      __VERIFIER_assert(1 <= i);
      __VERIFIER_assert(i <= n);
      __VERIFIER_assert(1 <= j);
      __VERIFIER_assert(j <= n);
      i = j;
      j = 2 * j;
    }
    if (l > 1) {
      __VERIFIER_assert(1 <= l);
      __VERIFIER_assert(l <= n);
      l = l - 1;
    } else {
      __VERIFIER_assert(1 <= r);
      __VERIFIER_assert(r <= n);
      r = r - 1;
    }
  }
  result = 0;
  return result;
}

