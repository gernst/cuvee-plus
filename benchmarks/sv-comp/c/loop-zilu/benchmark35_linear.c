// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark35_linear.c
// SV-COMP loop-zilu/benchmark35_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark35_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int x;
  __VERIFIER_assume(0 < N);
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  if (!(x >= 0)) {
    result = 0;
    return result;
  }
  while (x >= 0 && x < N) {
    x = x + 1;
  }
  assert(x >= N);
  result = 0;
  return result;
}

