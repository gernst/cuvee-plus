// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/array-2.c
// SV-COMP loops/array-2.yml, translated from benchmarks/sv-comp/dafny/loops/array-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array-2.c", 7, "reach_error"); }
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
  int tmp_1 = __VERIFIER_nondet_int();
  int SIZE = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int menor = __VERIFIER_nondet_int();
  SIZE = 1;
  menor = __VERIFIER_nondet_int();
  j = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && SIZE <= N && 0 < N && N <= 536870911);
  int Array[N];
  while (j < SIZE) {
    tmp_1 = __VERIFIER_nondet_int();
    Array[j] = tmp_1;
    if (Array[j] <= menor) {
      menor = Array[j];
    }
    j = j + 1;
  }
  __VERIFIER_assert(Array[0] > menor);
  result = 0;
  return result;
}

