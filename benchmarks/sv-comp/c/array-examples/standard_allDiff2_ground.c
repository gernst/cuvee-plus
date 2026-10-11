// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_allDiff2_ground.c
// SV-COMP array-examples/standard_allDiff2_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_allDiff2_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_allDiff2_ground.c", 7, "reach_error"); }
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
  int tmp_1 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int r = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int a[N];
  assume_abort_if_not(0 < N);
  r = 1;
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    a[i] = tmp_1;
    i = i + 1;
  }
  i = 1;
  while (i < N && r != 0) {
    j = i - 1;
    while (j >= 0 && r != 0) {
      if (a[i] == a[j]) {
        r = 1;
      }
      j = j - 1;
    }
    i = i + 1;
  }
  if (r != 0) {
    x = 0;
    while (x < N) {
      y = x + 1;
      while (y < N) {
        __VERIFIER_assert(a[x] != a[y]);
        y = y + 1;
      }
      x = x + 1;
    }
  }
  result = 0;
  return result;
}

