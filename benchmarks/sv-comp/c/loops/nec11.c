// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/nec11.c
// SV-COMP loops/nec11.yml, translated from benchmarks/sv-comp/dafny/loops/nec11.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern int __VERIFIER_nondet_int(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nec11.c", 7, "reach_error"); }
extern _Bool __VERIFIER_nondet_bool(void);
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
  _Bool tmp_1 = __VERIFIER_nondet_bool();
  int len = __VERIFIER_nondet_int();
  _Bool c = __VERIFIER_nondet_bool();
  int i = __VERIFIER_nondet_int();
  len = 0;
  tmp_1 = __VERIFIER_nondet_bool();
  c = tmp_1;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int a[N];
  while (c) {
    if (len == 4) {
      len = 0;
    }
    a[len] = 0;
    len = len + 1;
  }
  __VERIFIER_assert(len == 5);
  result = 1;
  return result;
}

