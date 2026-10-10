// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/egcd3-ll.c
// SV-COMP nla-digbench/egcd3-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/egcd3-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  int y;
  int a;
  int b;
  int p;
  int q;
  int r;
  int s;
  int c;
  int k;
  int temp;
  int d;
  int v;
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
    if (!(b != 0)) {
      break;
    }
    c = a;
    k = 0;
    while (1 != 0) {
      if (!(c >= b)) {
        break;
      }
      d = 1;
      v = b;
      while (1 != 0) {
        assert(a == y * r + x * p);
        assert(b == x * q + y * s);
        assert(a == k * b + c);
        assert(v == b * d);
        if (!(c >= 2 * v)) {
          break;
        }
        d = 2 * d;
        v = 2 * v;
      }
      c = c - v;
      k = k + d;
    }
    a = b;
    b = c;
    temp = p;
    p = q;
    q = temp - q * k;
    temp = r;
    r = s;
    s = temp - s * k;
  }
  assert(p * x - q * x + r * y - s * y == a);
  result = 0;
  return result;
}

