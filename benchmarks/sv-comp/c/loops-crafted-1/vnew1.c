// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/vnew1.c
// SV-COMP loops-crafted-1/vnew1.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/vnew1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int i;
  int k;
  int j;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  k = n;
  i = 0;
  while (i < n) {
    k = k - 1;
    i = i + 3;
  }
  j = 0;
  while (j < n / 3) {
    assert(k > 0);
    k = k - 1;
    j = j + 1;
  }
}

