// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/geo2-ll.c
// SV-COMP nla-digbench/geo2-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/geo2-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int z;
  int k;
  int x;
  int y;
  int c;
  z = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();
  x = 1;
  y = 1;
  c = 1;
  while (1 != 0) {
    assert(1 + x * z - x - z * y == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    x = x * z + 1;
    y = y * z;
  }
  assert(1 + x * z - x - z * y == 0);
  result = 0;
  return result;
}

