// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/prodbin-ll.c
// SV-COMP nla-digbench/prodbin-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/prodbin-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void assume_abort_if_not(int cond) {
  if (!(cond != 0)) {
    __VERIFIER_assume(false);
  }
}

int main(void) {
  int result;
  int a;
  int b;
  int x;
  int y;
  int z;
  a = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_int();
  assume_abort_if_not(b >= 1 ? 1 : 0);
  x = a;
  y = b;
  z = 0;
  while (1 != 0) {
    assert(z + x * y == a * b);
    if (!(y != 0)) {
      break;
    }
    if (y % 2 == 1) {
      z = z + x;
      y = y - 1;
    }
    x = 2 * x;
    y = y / 2;
  }
  assert(z == a * b);
  result = 0;
  return result;
}

