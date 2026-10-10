// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/in-de20.c
// SV-COMP loops-crafted-1/in-de20.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/in-de20.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int x;
  int y;
  int z;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
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
  assert(x == n);
}

