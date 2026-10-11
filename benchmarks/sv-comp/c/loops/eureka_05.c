// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/eureka_05.c
// SV-COMP loops/eureka_05.yml, translated from benchmarks/sv-comp/dafny/loops/eureka_05.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "eureka_05.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int lh = __VERIFIER_nondet_int();
  int rh = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int temp = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int Array[N];
  int array_1[N];
  assume_abort_if_not(0 < N);
  n = N;
  i = N - 1;
  while (i >= 0) {
    array_1[i] = i;
    i = i - 1;
  }
  lh = 0;
  while (lh < n) {
    rh = lh;
    j = lh + 1;
    while (j < n) {
      if (Array[j] < Array[rh]) {
        rh = j;
      }
      j = j + 1;
    }
    temp = Array[lh];
    Array[lh] = Array[rh];
    Array[rh] = temp;
    lh = lh + 1;
  }
  i = 0;
  while (i < N) {
    __VERIFIER_assert(array_1[i] == i);
    i = i + 1;
  }
}

