// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/terminator_03-2.c
// SV-COMP loops/terminator_03-2.yml, translated from benchmarks/sv-comp/dafny/loops/terminator_03-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int tmp_2;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  y = tmp_2;
  if (y > 0) {
    while (x < N) {
      x = x + y;
    }
  }
  assert(y <= 0 || y > 0 && x >= N);
  result = 0;
  return result;
}

