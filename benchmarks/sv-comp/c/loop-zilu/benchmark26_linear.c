// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark26_linear.c
// SV-COMP loop-zilu/benchmark26_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark26_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  if (!(x < y)) {
    result = 0;
    return result;
  }
  while (x < y) {
    x = x + 1;
  }
  assert(x == y);
  result = 0;
  return result;
}

