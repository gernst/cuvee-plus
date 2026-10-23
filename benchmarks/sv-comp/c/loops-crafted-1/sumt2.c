// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops-crafted-1/sumt2.c
// SV-COMP loops-crafted-1/sumt2.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/sumt2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sumt2.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= n);
  i = 0;
  j = 0;
  l = 0;
  while (l < n) {
    if (l % 2 == 0) {
      i = i + 1;
    } else {
      j = j + 1;
    }
    l = l + 1;
  }
  __VERIFIER_assert(i + j == l);
}

