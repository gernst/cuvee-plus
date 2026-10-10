// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/nest-if3.c
// SV-COMP loop-invgen/nest-if3.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/nest-if3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int k;
  int n;
  int l;
  n = __VERIFIER_nondet_int();
  l = __VERIFIER_nondet_int();
  if (!(l > 0)) {
    result = 0;
    return result;
  }
  k = 1;
  while (k < n) {
    i = l;
    while (i < n) {
      assert(1 <= i);
      i = i + 1;
    }
    tmp_1 = __VERIFIER_nondet_int();
    if (tmp_1 != 0) {
      l = l + 1;
    }
    k = k + 1;
  }
}

