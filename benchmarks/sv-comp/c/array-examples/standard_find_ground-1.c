// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-examples/standard_find_ground-1.c
// SV-COMP array-examples/standard_find_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_find_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_find_ground-1.c", 7, "reach_error"); }
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
  int e = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int tmp = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  assume_abort_if_not(0 < N);
  int a[N];
  e = __VERIFIER_nondet_int();
  i = 0;
  j = 0;
  while (j < N) {
    tmp = __VERIFIER_nondet_int();
    a[j] = tmp;
    j = j + 1;
  }
  while (i < N && a[i] != e) {
    i = i + 1;
  }
  x = 0;
  while (x < i) {
    __VERIFIER_assert(a[x] != e);
    x = x + 1;
  }
}

