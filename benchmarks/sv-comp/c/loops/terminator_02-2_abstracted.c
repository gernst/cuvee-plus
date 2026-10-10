// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/terminator_02-2_abstracted.c
// SV-COMP loops/terminator_02-2_abstracted.yml, translated from benchmarks/sv-comp/dafny/loops/terminator_02-2_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int x;
  int z;
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  z = tmp_2;
  if (!(x > -100)) {
    result = 0;
    return result;
  }
  if (!(z > 100)) {
    result = 0;
    return result;
  }
  if (((z > 100 ? 1 : 0) & (x < 100 ? 1 : 0)) != 0) {
    z = __VERIFIER_nondet_int();
    x = __VERIFIER_nondet_int();
  }
  if (((z > 100 ? 1 : 0) & (x < 100 ? 1 : 0)) != 0) {
    __VERIFIER_assume(false);
  }
  assert(x >= 100 || z <= 100);
  result = 0;
  return result;
}

