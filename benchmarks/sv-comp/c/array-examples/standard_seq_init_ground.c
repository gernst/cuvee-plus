// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-examples/standard_seq_init_ground.c
// SV-COMP array-examples/standard_seq_init_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_seq_init_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_seq_init_ground.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int a[N];
  assume_abort_if_not(0 < N);
  i = 1;
  a[0] = 7;
  while (i < N) {
    a[i] = a[i - 1] + 1;
    i = i + 1;
  }
  x = 1;
  while (x < N) {
    __VERIFIER_assert(a[x] >= a[x - 1]);
    x = x + 1;
  }
}

