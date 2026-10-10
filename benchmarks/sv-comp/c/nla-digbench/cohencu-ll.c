// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/cohencu-ll.c
// SV-COMP nla-digbench/cohencu-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/cohencu-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void assume_abort_if_not(int cond) {
  if (!(cond != 0)) {
    __VERIFIER_assume(false);
  }
}

int main(void) {
  int result;
  int a;
  int n;
  int x;
  int y;
  int z;
  a = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= a);
  n = 0;
  x = 0;
  y = 1;
  z = 6;
  while (1 != 0) {
    assert(z == 6 * n + 6);
    assert(y == 3 * n * n + 3 * n + 1);
    assert(x == n * n * n);
    assert(y * z - 18 * x - 12 * y + 2 * z - 6 == 0);
    assert(z * z - 12 * y - 6 * z + 12 == 0);
    if (!(n <= a)) {
      break;
    }
    n = n + 1;
    x = x + y;
    y = y + z;
    z = z + 6;
  }
  assert(z == 6 * n + 6);
  assert(6 * a * x - x * z + 12 * x == 0);
  assert(a * z - 6 * a - 2 * y + 2 * z - 10 == 0);
  assert(2 * y * y - 3 * x * z - 18 * x - 10 * y + 3 * z - 10 == 0);
  assert(z * z - 12 * y - 6 * z + 12 == 0);
  assert(y * z - 18 * x - 12 * y + 2 * z - 6 == 0);
  result = 0;
  return result;
}

