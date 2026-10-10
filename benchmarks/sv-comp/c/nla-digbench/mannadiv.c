// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/mannadiv.c
// SV-COMP nla-digbench/mannadiv.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/mannadiv.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void assume_abort_if_not(int cond) {
  if (!(cond != 0)) {
    __VERIFIER_assume(false);
  }
}

int main(void) {
  int result;
  int x1;
  int x2;
  int y1;
  int y2;
  int y3;
  x1 = __VERIFIER_nondet_int();
  x2 = __VERIFIER_nondet_int();
  assume_abort_if_not(x1 >= 0 ? 1 : 0);
  assume_abort_if_not(x2 != 0 ? 1 : 0);
  y1 = 0;
  y2 = 0;
  y3 = x1;
  while (1 != 0) {
    assert(y1 * x2 + y2 + y3 == x1);
    if (!(y3 != 0)) {
      break;
    }
    if (y2 + 1 == x2) {
      y1 = y1 + 1;
      y2 = 0;
      y3 = y3 - 1;
    } else {
      y2 = y2 + 1;
      y3 = y3 - 1;
    }
  }
  assert(y1 * x2 + y2 == x1);
  result = 0;
  return result;
}

