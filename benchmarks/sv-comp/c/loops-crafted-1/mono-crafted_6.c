// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops-crafted-1/mono-crafted_6.c
// SV-COMP loops-crafted-1/mono-crafted_6.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_6.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "mono-crafted_6.c", 7, "reach_error"); }
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
  int N = __VERIFIER_nondet_int();
  int K = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < K);
  assume_abort_if_not(N == 8 * K);
  x = 0;
  y = 4 * K;
  z = 0;
  x = 0;
  while (x < N) {
    if (x < N / 2) {
      x = x + 1;
    } else {
      if (x < 3 * N / 4) {
        x = x + 1;
      } else {
        x = x + 2;
      }
      y = y + 1;
    }
  }
  __VERIFIER_assert(x == N);
  result = 0;
  return result;
}

