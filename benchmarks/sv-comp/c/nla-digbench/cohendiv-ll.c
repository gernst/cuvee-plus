// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/cohendiv-ll.c
// SV-COMP nla-digbench/cohendiv-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/cohendiv-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  int y;
  int q;
  int r;
  int a;
  int b;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  __VERIFIER_assume(y >= 1);
  q = 0;
  r = x;
  a = 0;
  b = 0;
  while (1 != 0) {
    assert(b == y * a);
    assert(x == q * y + r);
    if (!(r >= y)) {
      break;
    }
    a = 1;
    b = y;
    while (1 != 0) {
      assert(b == y * a);
      assert(x == q * y + r);
      assert(r >= 0);
      if (!(r >= 2 * b)) {
        break;
      }
      assert(r >= 2 * y * a);
      a = 2 * a;
      b = 2 * b;
    }
    r = r - b;
    q = q + a;
  }
  assert(x == q * y + r);
  result = 0;
  return result;
}

