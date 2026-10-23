// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-examples/standard_copy2_ground-2.c
// SV-COMP array-examples/standard_copy2_ground-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_copy2_ground-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_copy2_ground-2.c", 7, "reach_error"); }
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
  int v = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 134217727);
  assume_abort_if_not(0 < N);
  int a1[N], a2[N], a3[N];
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    a1[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a2[i] = a1[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a3[i] = a2[i];
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    __VERIFIER_assert(a1[x] == a3[x]);
    x = x + 1;
  }
}

