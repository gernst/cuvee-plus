// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/egcd2-ll.c
// SV-COMP nla-digbench/egcd2-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/egcd2-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  int xy;
  int yy;
  int temp;
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
  c = 0;
  k = 0;
  xy = x * y;
  yy = y * y;
  while (1 != 0) {
    if (!(b != 0)) {
      break;
    }
    c = a;
    k = 0;
    while (1 != 0) {
      assert(a == k * b + c);
      assert(a == y * r + x * p);
      assert(b == x * q + y * s);
      assert(q * xy + s * yy - q * x - b * y - s * y + b == 0);
      if (!(c >= b)) {
        break;
      }
      c = c - b;
      k = k + 1;
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
  assert(q * x + s * y == 0);
  assert(p * x + r * y == a);
  result = a;
  return result;
}

