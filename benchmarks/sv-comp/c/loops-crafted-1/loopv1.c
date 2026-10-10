// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/loopv1.c
// SV-COMP loops-crafted-1/loopv1.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/loopv1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int i;
  int j;
  int c;
  n = __VERIFIER_nondet_int();
  i = 0;
  j = 0;
  while (i < n) {
    c = __VERIFIER_nondet_int();
    if (c != 0) {
      i = i + 6;
    } else {
      i = i + 3;
    }
  }
  assert(i % 3 == 0);
}

