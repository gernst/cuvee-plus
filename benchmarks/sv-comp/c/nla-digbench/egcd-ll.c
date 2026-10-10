// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/egcd-ll.c
// SV-COMP nla-digbench/egcd-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/egcd-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int a;
  int b;
  int p;
  int q;
  int r;
  int s;
  int x;
  int y;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  __VERIFIER_assume(x >= 1);
  __VERIFIER_assume(y >= 1);
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;
  while (1 != 0) {
    assert(1 == p * s - r * q);
    assert(a == y * r + x * p);
    assert(b == x * q + y * s);
    if (!(a != b)) {
      break;
    }
    if (a > b) {
      a = a - b;
      p = p - q;
      r = r - s;
    } else {
      b = b - a;
      q = q - p;
      s = s - r;
    }
  }
  assert(a - b == 0);
  assert(p * x + r * y - b == 0);
  assert(q * r - p * s + 1 == 0);
  assert(q * x + s * y - b == 0);
  result = 0;
  return result;
}

