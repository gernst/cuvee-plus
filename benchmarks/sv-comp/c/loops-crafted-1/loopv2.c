// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/loopv2.c
// SV-COMP loops-crafted-1/loopv2.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/loopv2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int n;
  int i;
  int j;
  int k;
  n = __VERIFIER_nondet_int();
  i = 0;
  j = 0;
  while (i < n) {
    i = i + 4;
    j = i + 2;
  }
  k = i;
  while (j % 2 == 0) {
    j = j - 4;
    k = k - 4;
  }
  assert(k % 2 == 0);
  result = 0;
  return result;
}

