// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/rewrev.c
// SV-COMP array-tiling/rewrev.yml, translated from benchmarks/sv-comp/dafny/array-tiling/rewrev.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "rewrev.c", 7, "reach_error"); }
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
  S = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && S <= N && N <= 536870911);
  int a[N];
  if (S > 1) {
    i = S - 2;
    while (i >= -1) {
      if (i >= 0) {
        a[i] = 7;
      }
      a[i + 1] = 3;
      i = i - 1;
    }
    i = 0;
    while (i < S) {
      __VERIFIER_assert(a[i] >= 2);
      i = i + 1;
    }
  }
}

