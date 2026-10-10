// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-new/half.c
// SV-COMP loop-new/half.yml, translated from benchmarks/sv-comp/dafny/loop-new/half.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int n;
  int k;
  i = 0;
  n = 0;
  k = __VERIFIER_nondet_int();
  i = 0;
  while (i < 2 * k) {
    if (i % 2 == 0) {
      n = n + 1;
    }
    i = i + 1;
  }
  assert(k < 0 || n == k);
}

