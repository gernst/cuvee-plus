// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_copy1_ground-1.c
// SV-COMP array-examples/standard_copy1_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_copy1_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_copy1_ground-1.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int tmp = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int a1[N];
  int a2[N];
  assume_abort_if_not(0 < N);
  a = 0;
  while (a < N) {
    tmp = __VERIFIER_nondet_int();
    a1[a] = tmp;
    a = a + 1;
  }
  i = 0;
  while (i < N) {
    a2[i] = a1[i];
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    __VERIFIER_assert(a1[x] == a2[x]);
    x = x + 1;
  }
}

