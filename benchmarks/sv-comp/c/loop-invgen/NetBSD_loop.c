// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/NetBSD_loop.c
// SV-COMP loop-invgen/NetBSD_loop.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/NetBSD_loop.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "NetBSD_loop.c", 7, "reach_error"); }
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
  int M = __VERIFIER_nondet_int();
  int p = __VERIFIER_nondet_int();
  M = __VERIFIER_nondet_int();
  assume_abort_if_not(M <= 1073741823);
  if (!(M > 0)) {
    return;
  }
  p = 0;
  while (p <= M) {
    __VERIFIER_assert(0 <= p);
    __VERIFIER_assert(p < M + 1);
    p = p + 1;
  }
}

