// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/in-de52.c
// SV-COMP loops-crafted-1/in-de52.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/in-de52.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int n;
  int x;
  int y;
  int z;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  n = tmp_1;
  x = n;
  y = 0;
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  z = y;
  while (z > 0) {
    x = x + 1;
    z = z - 1;
  }
  while (y > 0) {
    y = y - 1;
    z = z + 1;
  }
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  while (z > 0) {
    y = y - 1;
    z = z - 1;
  }
  assert(y == 0);
  result = 0;
  return result;
}

