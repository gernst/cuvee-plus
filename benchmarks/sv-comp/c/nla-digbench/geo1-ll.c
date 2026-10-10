// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/geo1-ll.c
// SV-COMP nla-digbench/geo1-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/geo1-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void assume_abort_if_not(int cond) {
  if (!(cond != 0)) {
    __VERIFIER_assume(false);
  }
}

int main(void) {
  int result;
  int z;
  int k;
  int x;
  int y;
  int c;
  z = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();
  assume_abort_if_not(z >= 1 ? 1 : 0);
  assume_abort_if_not(k >= 1 ? 1 : 0);
  x = 1;
  y = z;
  c = 1;
  while (1 != 0) {
    assert(x * z - x - y + 1 == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    x = x * z + 1;
    y = y * z;
  }
  x = x * (z - 1);
  assert(1 + x - y == 0);
  result = 0;
  return result;
}

