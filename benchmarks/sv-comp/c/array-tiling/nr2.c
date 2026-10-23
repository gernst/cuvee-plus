// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-tiling/nr2.c
// SV-COMP array-tiling/nr2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/nr2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nr2.c", 7, "reach_error"); }
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
  int C = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int MINVAL = __VERIFIER_nondet_int();
  C = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && C / 2 < N && C <= N && N <= 536870911);
  int a[N];
  if (C > 1) {
    MINVAL = 2;
    if (C % 2 != 0) {
      return;
    }
    i = 1;
    while (i <= C / 2) {
      j = 2;
      while (j >= 1) {
        if (j >= MINVAL) {
          a[i * 2 - j] = j;
        } else {
          a[i * 2 - j] = 0;
        }
        j = j - 1;
      }
      i = i + 1;
    }
    i = 0;
    while (i < C) {
      __VERIFIER_assert(a[i] >= MINVAL || a[i] == 0);
      i = i + 1;
    }
  }
}

