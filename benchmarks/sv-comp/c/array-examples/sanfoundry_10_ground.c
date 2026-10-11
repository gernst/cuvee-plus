// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sanfoundry_10_ground.c
// SV-COMP array-examples/sanfoundry_10_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/sanfoundry_10_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sanfoundry_10_ground.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int pos = __VERIFIER_nondet_int();
  int element = __VERIFIER_nondet_int();
  int found = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < n);
  element = __VERIFIER_nondet_int();
  found = 0;
  i = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && n <= N && n - 1 <= N && N <= 536870911);
  int vectorx[N];
  while (i < n) {
    v = __VERIFIER_nondet_int();
    vectorx[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < n && found == 0) {
    if (vectorx[i] == element) {
      found = 1;
      pos = i;
    }
    i = i + 1;
  }
  if (found != 0) {
    i = pos;
    while (i < n - 1) {
      vectorx[i] = vectorx[i + 1];
      i = i + 1;
    }
  }
  if (found != 0) {
    x = 0;
    while (x < pos) {
      __VERIFIER_assert(vectorx[x] != element);
      x = x + 1;
    }
  }
}

