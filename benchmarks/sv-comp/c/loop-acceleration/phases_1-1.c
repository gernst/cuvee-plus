// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-acceleration/phases_1-1.c
// SV-COMP loop-acceleration/phases_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/phases_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "phases_1-1.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  assume_abort_if_not(65520 < N);
  x = 0;
  while (x < N) {
    if (x < 65520) {
      x = x + 1;
    } else {
      x = x + 2;
    }
  }
  __VERIFIER_assert(x % 2 == 0);
}

