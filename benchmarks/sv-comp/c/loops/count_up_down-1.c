// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/count_up_down-1.c
// SV-COMP loops/count_up_down-1.yml, translated from benchmarks/sv-comp/dafny/loops/count_up_down-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int x;
  int y;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  x = n;
  y = 0;
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  assert(y == n);
}

