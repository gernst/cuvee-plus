// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops-crafted-1/sumt7.c
// SV-COMP loops-crafted-1/sumt7.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/sumt7.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sumt7.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  int v4 = __VERIFIER_nondet_int();
  n = 0;
  i = 0;
  k = 0;
  j = 0;
  l = 0;
  v1 = 0;
  v2 = 0;
  v3 = 0;
  v4 = 0;
  n = __VERIFIER_nondet_int();
  while (l < n) {
    if (!(l % 7 != 0)) {
      v1 = v1 + 1;
    } else if (!(l % 6 != 0)) {
      v2 = v2 + 1;
    } else if (!(l % 5 != 0)) {
      v3 = v3 + 1;
    } else if (!(l % 4 != 0)) {
      v4 = v4 + 1;
    } else if (!(l % 3 != 0)) {
      i = i + 1;
    } else if (!(l % 2 != 0)) {
      j = j + 1;
    } else {
      k = k + 1;
    }
    l = l + 1;
    __VERIFIER_assert(i + j + k + v1 + v2 + v3 + v4 == l);
  }
  result = 0;
  return result;
}

