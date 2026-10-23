// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-tiling/pr2.c
// SV-COMP array-tiling/pr2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/pr2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "pr2.c", 7, "reach_error"); }
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
  int MINVAL = __VERIFIER_nondet_int();
  int V2 = __VERIFIER_nondet_int();
  int V1 = __VERIFIER_nondet_int();
  C = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && C / 2 < N && C <= N && N <= 536870911);
  int a[N];
  if (C > 1) {
    MINVAL = __VERIFIER_nondet_int();
    V2 = 3;
    V1 = 1;
    if (C % 2 != 0) {
      return;
    }
    i = 1;
    while (i <= C / 2) {
      if (V2 >= MINVAL) {
        a[i * 2 - 2] = V2;
      } else {
        a[i * 2 - 2] = 0;
      }
      if (V1 >= MINVAL) {
        a[i * 2 - 1] = V1;
      } else {
        a[i * 2 - 1] = 0;
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

