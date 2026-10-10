// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/count_up_down-2.c
// SV-COMP loops/count_up_down-2.yml, translated from benchmarks/sv-comp/dafny/loops/count_up_down-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int n;
  int x;
  int y;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  n = tmp_1;
  x = n;
  y = 0;
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  assert(y != n);
}

