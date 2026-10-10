// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/divbin.c
// SV-COMP nla-digbench/divbin.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/divbin.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int A;
  int B;
  int q;
  int r;
  int b;
  A = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= A);
  B = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= B);
  __VERIFIER_assume(B >= 1);
  q = 0;
  r = A;
  b = B;
  while (1 != 0) {
    if (!(r >= b)) {
      break;
    }
    b = 2 * b;
  }
  while (1 != 0) {
    assert(A == q * b + r);
    if (!(b != B)) {
      break;
    }
    q = 2 * q;
    b = b / 2;
    if (r >= b) {
      q = q + 1;
      r = r - b;
    }
  }
  assert(A == q * b + r);
  result = 0;
  return result;
}

