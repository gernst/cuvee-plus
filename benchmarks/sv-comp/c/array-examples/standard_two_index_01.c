// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_two_index_01.c
// SV-COMP array-examples/standard_two_index_01.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_two_index_01.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_two_index_01.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int tmp = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int a[N];
  int b[N];
  assume_abort_if_not(0 < N);
  i = 0;
  j = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    b[i] = tmp;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[j] = b[i];
    i = i + 1;
    j = j + 1;
  }
  i = 0;
  j = 0;
  while (i < N) {
    __VERIFIER_assert(a[j] == b[j]);
    i = i + 1;
    j = j + 1;
  }
}

