// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/break-1.c
// SV-COMP array-lopstr16/break-1.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/break-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int c;
  _Bool s[];
  __VERIFIER_assume(0 < N);
  c = __VERIFIER_nondet_int();
  i = 0;
  while (i < N) {
    if (c > 5) {
      break;
    }
    s[i] = true;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (c <= 5) {
      assert(s[i]);
    }
    i = i + 1;
  }
}

