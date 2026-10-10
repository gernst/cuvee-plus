// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/mono-crafted_10.c
// SV-COMP loops-crafted-1/mono-crafted_10.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_10.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int M;
  int x;
  int y;
  int z;
  x = 0;
  __VERIFIER_assume(0 < M);
  y = __VERIFIER_nondet_int();
  __VERIFIER_assume(M <= y);
  z = M;
  while (x < y) {
    if (x >= M) {
      z = z + 1;
    }
    x = x + 1;
  }
  assert(z == x);
  result = 0;
  return result;
}

