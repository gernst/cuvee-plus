// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark52_polynomial.c
// SV-COMP loop-zilu/benchmark52_polynomial.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark52_polynomial.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int i;
  __VERIFIER_assume(0 < N);
  tmp_1 = __VERIFIER_nondet_int();
  i = tmp_1;
  if (!(i < 10 && i > -10)) {
    result = 0;
    return result;
  }
  while (i * i < N) {
    i = i + 1;
  }
  assert(i == 10);
  result = 0;
  return result;
}

