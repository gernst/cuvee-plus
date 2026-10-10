// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/prod4br-ll.c
// SV-COMP nla-digbench/prod4br-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/prod4br-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  int y;
  int a;
  int b;
  int p;
  int q;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  __VERIFIER_assume(y >= 1);
  a = x;
  b = y;
  p = 1;
  q = 0;
  while (1 != 0) {
    assert(q + a * b * p == x * y);
    if (!(a != 0 && b != 0)) {
      break;
    }
    if (a % 2 == 0 && b % 2 == 0) {
      a = a / 2;
      b = b / 2;
      p = 4 * p;
    } else if (a % 2 == 1 && b % 2 == 0) {
      a = a - 1;
      q = q + b * p;
    } else if (a % 2 == 0 && b % 2 == 1) {
      b = b - 1;
      q = q + a * p;
    } else {
      a = a - 1;
      b = b - 1;
      q = q + (a + b + 1) * p;
    }
  }
  assert(q == x * y);
  assert(a * b == 0);
  result = 0;
  return result;
}

