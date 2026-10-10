// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/lcm2.c
// SV-COMP nla-digbench/lcm2.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/lcm2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int a;
  int b;
  int x;
  int y;
  int u;
  int v;
  a = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= a);
  b = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= b);
  __VERIFIER_assume(a >= 1);
  __VERIFIER_assume(b >= 1);
  x = a;
  y = b;
  u = b;
  v = a;
  while (1 != 0) {
    assert(x * u + y * v == 2 * a * b);
    if (!(x != y)) {
      break;
    }
    if (x > y) {
      x = x - y;
      v = v + u;
    } else {
      y = y - x;
      u = u + v;
    }
  }
  assert(x * u + y * v == 2 * a * b);
  result = 0;
  return result;
}

