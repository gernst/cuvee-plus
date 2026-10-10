// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_4-2_abstracted.c
// SV-COMP loop-acceleration/simple_4-2_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_4-2_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  x = 268435440;
  if (x > 0) {
    x = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= x);
  }
  if (x > 0) {
    __VERIFIER_assume(false);
  }
  assert(!(x % 2 != 0));
}

