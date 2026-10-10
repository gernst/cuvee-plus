// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/fermat2-ll.c
// SV-COMP nla-digbench/fermat2-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/fermat2-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int A;
  int R;
  int u;
  int v;
  int r;
  A = __VERIFIER_nondet_int();
  R = __VERIFIER_nondet_int();
  __VERIFIER_assume((R - 1) * (R - 1) < A);
  __VERIFIER_assume(A % 2 == 1);
  u = 2 * R + 1;
  v = 1;
  r = R * R - A;
  while (1 != 0) {
    assert(4 * (A + r) == u * u - v * v - 2 * u + 2 * v);
    if (!(r != 0)) {
      break;
    }
    if (r > 0) {
      r = r - v;
      v = v + 2;
    } else {
      r = r + u;
      u = u + 2;
    }
  }
  assert(4 * A == u * u - v * v - 2 * u + 2 * v);
  result = 0;
  return result;
}

