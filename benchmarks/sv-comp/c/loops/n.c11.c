// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops/n.c11.c
// SV-COMP loops/n.c11.yml, translated from benchmarks/sv-comp/dafny/loops/n.c11.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern int __VERIFIER_nondet_int(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "n.c11.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  len = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int a[N];
  while (1) {
    tmp_1 = __VERIFIER_nondet_bool();
    if (!tmp_1) {
      break;
    }
    if (len == 4) {
      len = 0;
    }
    a[len] = 0;
    len = len + 1;
  }
  __VERIFIER_assert(len >= 0 && len < 5);
  result = 1;
  return result;
}

