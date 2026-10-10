// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark37_conjunctive.c
// SV-COMP loop-zilu/benchmark37_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark37_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int x;
  int y;
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  y = tmp_2;
  if (!(x == y && x >= 0)) {
    result = 0;
    return result;
  }
  while (x > 0) {
    x = x - 1;
    y = y - 1;
  }
  assert(y >= 0);
  result = 0;
  return result;
}

