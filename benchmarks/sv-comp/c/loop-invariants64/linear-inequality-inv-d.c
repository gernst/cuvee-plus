// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-invariants64/linear-inequality-inv-d.c
// SV-COMP loop-invariants64/linear-inequality-inv-d.yml, translated from benchmarks/sv-comp/dafny/loop-invariants64/linear-inequality-inv-d.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "linear-inequality-inv-d.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  int s = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= M && M <= 32767);
  assume_abort_if_not(0 < n && n <= M);
  v = 0;
  s = 0;
  i = 0;
  while (i < n) {
    v = __VERIFIER_nondet_int();
    assume_abort_if_not(0 <= v && v <= M);
    s = s + v;
    i = i + 1;
  }
  __VERIFIER_assert(s >= v);
  __VERIFIER_assert(s <= M * M);
}

