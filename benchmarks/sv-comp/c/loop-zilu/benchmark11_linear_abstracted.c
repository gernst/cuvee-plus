// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark11_linear_abstracted.c
// SV-COMP loop-zilu/benchmark11_linear_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark11_linear_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  if (x < n) {
    x = __VERIFIER_nondet_int();
    if (!(x < n)) {
      __VERIFIER_assume(false);
    }
    if (x < n) {
      x = x + 1;
    }
    if (x < n) {
      __VERIFIER_assume(false);
    }
  }
  assert(x == n);
  result = 0;
  return result;
}

