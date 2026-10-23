// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-invgen/id_build.c
// SV-COMP loop-invgen/id_build.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/id_build.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "id_build.c", 7, "reach_error"); }
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
  int offset = __VERIFIER_nondet_int();
  int length = __VERIFIER_nondet_int();
  int nlen = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  nlen = tmp_1;
  i = 0;
  while (i < nlen) {
    j = 0;
    while (j < 8) {
      __VERIFIER_assert(0 <= nlen - 1 - i);
      __VERIFIER_assert(nlen - 1 - i < nlen);
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

