// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/revcpyswp2.c
// SV-COMP array-tiling/revcpyswp2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/revcpyswp2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "revcpyswp2.c", 7, "reach_error"); }
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
  int tmp = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  S = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && S <= N && N <= 134217727);
  int a[N];
  int b[N];
  int ac[N];
  int bc[N];
  if (S > 1) {
    i = 0;
    while (i < S) {
      v = __VERIFIER_nondet_int();
      ac[i] = v;
      v = __VERIFIER_nondet_int();
      bc[i] = v;
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      a[i] = ac[S - i - 1];
      b[i] = bc[S - i - 1];
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      tmp = a[i];
      a[i] = b[i];
      b[i] = tmp;
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      tmp = a[i];
      a[i] = b[i];
      b[i] = tmp;
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      __VERIFIER_assert(a[i] == ac[S - i - 1]);
      i = i + 1;
    }
  }
}

