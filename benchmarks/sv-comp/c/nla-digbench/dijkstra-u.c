// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/dijkstra-u.c
// SV-COMP nla-digbench/dijkstra-u.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/dijkstra-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int n;
  int p;
  int q;
  int r;
  int h;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  p = 0;
  q = 1;
  r = n;
  h = 0;
  while (1 != 0) {
    if (!(q <= n)) {
      break;
    }
    q = 4 * q;
  }
  while (1 != 0) {
    assert(r < 2 * p + q);
    assert(p * p + r * q == n * q);
    assert(
      h * h * h - 12 * h * n * q + 16 * n * p * q - h * q * q - 4 * p * q * q
        + 12 * h * q * r
        - 16 * p * q * r
        == 0);
    assert(
      h * h * n - 4 * h * n * p + 4 * (n * n) * q - n * q * q - h * h * r
        + 4 * h * p * r
        - 8 * n * q * r
        + q * q * r
        + 4 * q * r * r
        == 0);
    assert(
      h * h * p - 4 * h * n * q + 4 * n * p * q - p * q * q + 4 * h * q * r
        - 4 * p * q * r
        == 0);
    assert(p * p - n * q + q * r == 0);
    if (!(q != 1)) {
      break;
    }
    q = q / 4;
    h = p + q;
    p = p / 2;
    if (r >= h) {
      p = p + q;
      r = r - h;
    }
  }
  assert(
    h * h * h - 12 * h * n + 16 * n * p + 12 * h * r - 16 * p * r - h - 4 * p
      == 0);
  assert(p * p - n + r == 0);
  assert(h * h * p - 4 * h * n + 4 * n * p + 4 * h * r - 4 * p * r - p == 0);
  result = 0;
  return result;
}

