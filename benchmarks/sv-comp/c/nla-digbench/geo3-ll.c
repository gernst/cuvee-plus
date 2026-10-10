// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/geo3-ll.c
// SV-COMP nla-digbench/geo3-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/geo3-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int z;
  int a;
  int k;
  int x;
  int y;
  int c;
  int az;
  z = __VERIFIER_nondet_int();
  a = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();
  x = a;
  y = 1;
  c = 1;
  az = a * z;
  while (1 != 0) {
    assert(z * x - x + a - az * y == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    x = x * z + a;
    y = y * z;
  }
  assert(z * x - x + a - az * y == 0);
  result = x;
  return result;
}

