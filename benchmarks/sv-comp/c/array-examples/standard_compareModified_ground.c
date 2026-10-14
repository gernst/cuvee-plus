// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-examples/standard_compareModified_ground.c
// SV-COMP array-examples/standard_compareModified_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_compareModified_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_compareModified_ground.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  int rv = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 134217727);
  assume_abort_if_not(0 < N);
  int a[N], b[N], c[N];
  i = 0;
  rv = 1;
  j = 0;
  while (j < N) {
    v = __VERIFIER_nondet_int();
    a[j] = v;
    v = __VERIFIER_nondet_int();
    b[j] = v;
    j = j + 1;
  }
  while (i < N) {
    if (a[i] != b[i]) {
      rv = 0;
    }
    c[i] = a[i];
    i = i + 1;
  }
  if (rv != 0) {
    x = 0;
    while (x < N) {
      __VERIFIER_assert(a[x] == b[x]);
      x = x + 1;
    }
  }
  x = 0;
  while (x < N) {
    __VERIFIER_assert(a[x] == c[x]);
    x = x + 1;
  }
}

