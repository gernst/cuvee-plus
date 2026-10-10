// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark11_linear.c
// SV-COMP loop-zilu/benchmark11_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark11_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int x;
  int n;
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  n = tmp_2;
  if (!(x == 0 && n > 0)) {
    result = 0;
    return result;
  }
  while (x < n) {
    x = x + 1;
  }
  assert(x == n);
  result = 0;
  return result;
}

