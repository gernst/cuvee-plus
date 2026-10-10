// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/ps2-ll.c
// SV-COMP nla-digbench/ps2-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/ps2-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void assume_abort_if_not(int cond) {
  if (!(cond != 0)) {
    __VERIFIER_assume(false);
  }
}

int main(void) {
  int result;
  int k;
  int y;
  int x;
  int c;
  k = __VERIFIER_nondet_int();
  y = 0;
  x = 0;
  c = 0;
  while (1 != 0) {
    assert(y * y - 2 * x + y == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    y = y + 1;
    x = y + x;
  }
  assert(y * y - 2 * x + y == 0);
  result = 0;
  return result;
}

