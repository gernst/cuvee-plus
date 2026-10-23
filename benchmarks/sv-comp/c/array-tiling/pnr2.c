// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-tiling/pnr2.c
// SV-COMP array-tiling/pnr2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/pnr2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "pnr2.c", 7, "reach_error"); }
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
  int S = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int value = __VERIFIER_nondet_int();
  S = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && S / 2 < N && S <= N && N <= 536870911);
  int a[N];
  if (S > 1) {
    if (S % 2 != 0) {
      return;
    }
    i = 1;
    while (i <= S / 2) {
      value = __VERIFIER_nondet_int();
      if (value != 0) {
        a[i * 2 - 2] = value;
      } else {
        a[i * 2 - 2] = 10;
      }
      value = __VERIFIER_nondet_int();
      if (value != 0) {
        a[i * 2 - 1] = value;
      } else {
        a[i * 2 - 1] = 10;
      }
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      __VERIFIER_assert(a[i] != 0);
      i = i + 1;
    }
  }
}

