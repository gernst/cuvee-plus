// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_two_index_06.c
// SV-COMP array-examples/standard_two_index_06.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_two_index_06.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_two_index_06.c", 7, "reach_error"); }
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
  int j = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  assume_abort_if_not(0 < N);
  int a[N], b[N];
  i = 0;
  j = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    b[i] = tmp_1;
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    a[j] = b[i];
    i = i + 6;
    j = j + 1;
  }
  i = 1;
  j = 0;
  while (i < N) {
    __VERIFIER_assert(a[j] == b[6 * j + 1]);
    i = i + 6;
    j = j + 1;
  }
  result = 0;
  return result;
}

