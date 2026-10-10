// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/id_trans.c
// SV-COMP loop-invgen/id_trans.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/id_trans.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int idBitLength;
  int material_length;
  int nlen;
  int j;
  int k;
  nlen = __VERIFIER_nondet_int();
  idBitLength = __VERIFIER_nondet_int();
  material_length = __VERIFIER_nondet_int();
  if (nlen != idBitLength / 32) {
    result = 0;
    return result;
  }
  j = 0;
  while (j < idBitLength / 8 && j < material_length) {
    assert(0 <= j);
    assert(j < material_length);
    assert(0 <= j / 4);
    assert(j / 4 < nlen);
    j = j + 1;
  }
  result = 0;
  return result;
}

