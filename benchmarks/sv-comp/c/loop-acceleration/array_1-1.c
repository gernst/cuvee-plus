// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/array_1-1.c
// SV-COMP loop-acceleration/array_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/array_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_1-1.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int A[N];
  assume_abort_if_not(0 < N);
  i = 0;
  while (i < N) {
    A[i] = i;
    i = i + 1;
  }
  __VERIFIER_assert(A[N - 1] != N - 1);
}

