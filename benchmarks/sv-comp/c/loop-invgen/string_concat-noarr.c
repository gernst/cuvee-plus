// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/string_concat-noarr.c
// SV-COMP loop-invgen/string_concat-noarr.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/string_concat-noarr.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int b;
  __VERIFIER_assume(0 < N);
  i = 0;
  b = __VERIFIER_nondet_int();
  while (b != 0 && i < N) {
    i = i + 1;
    b = __VERIFIER_nondet_int();
  }
  if (i >= 100) {
    __VERIFIER_assume(false);
  }
  j = 0;
  b = __VERIFIER_nondet_int();
  while (b != 0 && i < N) {
    i = i + 1;
    j = j + 1;
    b = __VERIFIER_nondet_int();
  }
  if (j >= 100) {
    __VERIFIER_assume(false);
  }
  assert(i < 200);
}

