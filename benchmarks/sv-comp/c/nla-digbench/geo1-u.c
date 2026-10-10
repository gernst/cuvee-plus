// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/geo1-u.c
// SV-COMP nla-digbench/geo1-u.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/geo1-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int z;
  int k;
  int x;
  int y;
  int c;
  z = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= z);
  k = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= k);
  x = 1;
  y = z;
  c = 1;
  while (1 != 0) {
    assert(x * z - x - y + 1 == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    x = x * z + 1;
    y = y * z;
  }
  x = x * (z - 1);
  assert(1 + x - y == 0);
  result = 0;
  return result;
}

