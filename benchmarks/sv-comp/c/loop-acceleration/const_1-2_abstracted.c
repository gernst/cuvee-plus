// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/const_1-2_abstracted.c
// SV-COMP loop-acceleration/const_1-2_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/const_1-2_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  int y;
  int y__VERIFIER_LA_tmp0;
  int __VERIFIER_LA_iterations0;
  int x__VERIFIER_LA_old_tmp0;
  int y__VERIFIER_LA_old_tmp0;
  x = 1;
  y = 0;
  if (y < 1024) {
    y__VERIFIER_LA_tmp0 = y;
    __VERIFIER_LA_iterations0 = (1024 - y__VERIFIER_LA_tmp0) / 1;
    x__VERIFIER_LA_old_tmp0 = x;
    x = __VERIFIER_LA_iterations0 * 0 + x__VERIFIER_LA_old_tmp0 * 0 + 0;
    y__VERIFIER_LA_old_tmp0 = y;
    y = __VERIFIER_LA_iterations0 * 1 + y__VERIFIER_LA_old_tmp0;
  }
  assert(x == 1);
}

