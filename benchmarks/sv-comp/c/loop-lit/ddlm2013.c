// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/ddlm2013.c
// SV-COMP loop-lit/ddlm2013.yml, translated from benchmarks/sv-comp/dafny/loop-lit/ddlm2013.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "ddlm2013.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int flag = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  flag = tmp_1;
  a = 0;
  b = 0;
  j = 1;
  if (flag != 0) {
    i = 0;
  } else {
    i = 1;
  }
  while (1) {
    tmp_2 = __VERIFIER_nondet_int();
    if (!(tmp_2 != 0)) {
      break;
    }
    a = a + 1;
    b = b + (j - i);
    i = i + 2;
    if (i % 2 == 0) {
      j = j + 2;
    } else {
      j = j + 1;
    }
  }
  if (flag != 0) {
    __VERIFIER_assert(a == b);
  }
  result = 0;
  return result;
}

