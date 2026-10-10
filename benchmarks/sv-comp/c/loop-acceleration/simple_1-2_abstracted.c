// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_1-2_abstracted.c
// SV-COMP loop-acceleration/simple_1-2_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_1-2_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  int x__VERIFIER_LA_tmp0;
  int __VERIFIER_LA_iterations0;
  int x__VERIFIER_LA_old_tmp0;
  x = 0;
  if (x < 268435455) {
    x__VERIFIER_LA_tmp0 = x;
    __VERIFIER_LA_iterations0 = (268435455 - x__VERIFIER_LA_tmp0) / 2;
    x__VERIFIER_LA_old_tmp0 = x;
    x = __VERIFIER_LA_iterations0 * 2 + x__VERIFIER_LA_old_tmp0;
  }
  assert(!(x % 2 != 0));
}

