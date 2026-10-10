// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/sumt3.c
// SV-COMP loops-crafted-1/sumt3.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/sumt3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int i;
  int j;
  int k;
  int l;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  i = 0;
  j = 0;
  k = 0;
  l = 0;
  while (l < n) {
    if (l % 3 == 0) {
      i = i + 1;
    } else if (l % 2 == 0) {
      j = j + 1;
    } else {
      k = k + 1;
    }
    l = l + 1;
  }
  assert(i + j + k == l);
}

