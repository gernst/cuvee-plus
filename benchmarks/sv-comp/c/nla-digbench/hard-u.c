// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/hard-u.c
// SV-COMP nla-digbench/hard-u.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/hard-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int A;
  int B;
  int r;
  int d;
  int p;
  int q;
  A = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= A);
  B = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= B);
  __VERIFIER_assume(B >= 1);
  r = A;
  d = B;
  p = 1;
  q = 0;
  while (1 != 0) {
    assert(q == 0);
    assert(r == A);
    assert(d == B * p);
    if (!(r >= d)) {
      break;
    }
    d = 2 * d;
    p = 2 * p;
  }
  while (1 != 0) {
    assert(A == q * B + r);
    assert(d == B * p);
    if (!(p != 1)) {
      break;
    }
    d = d / 2;
    p = p / 2;
    if (r >= d) {
      r = r - d;
      q = q + p;
    }
  }
  assert(A == d * q + r);
  assert(B == d);
  result = 0;
  return result;
}

