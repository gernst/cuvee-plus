// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark32_linear.c
// SV-COMP loop-zilu/benchmark32_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark32_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  _Bool tmp_2;
  int x;
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  if (!(x == 1 || x == 2)) {
    result = 0;
    return result;
  }
  while (true) {
    tmp_2 = __VERIFIER_nondet_bool();
    if (!tmp_2) {
      break;
    }
    if (x == 1) {
      x = 2;
    } else if (x == 2) {
      x = 1;
    }
  }
  assert(x <= 8);
  result = 0;
  return result;
}

