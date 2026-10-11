// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/id_trans.c
// SV-COMP loop-invgen/id_trans.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/id_trans.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "id_trans.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int idBitLength = __VERIFIER_nondet_int();
  int material_length = __VERIFIER_nondet_int();
  int nlen = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  nlen = __VERIFIER_nondet_int();
  idBitLength = __VERIFIER_nondet_int();
  material_length = __VERIFIER_nondet_int();
  if (nlen != idBitLength / 32) {
    result = 0;
    return result;
  }
  j = 0;
  while (j < idBitLength / 8 && j < material_length) {
    __VERIFIER_assert(0 <= j);
    __VERIFIER_assert(j < material_length);
    __VERIFIER_assert(0 <= j / 4);
    __VERIFIER_assert(j / 4 < nlen);
    j = j + 1;
  }
  result = 0;
  return result;
}

