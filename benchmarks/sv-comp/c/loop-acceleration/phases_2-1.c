// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/phases_2-1.c
// SV-COMP loop-acceleration/phases_2-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/phases_2-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int x;
  int y;
  x = 1;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  y = tmp_1;
  if (!(y > 0)) {
    result = 0;
    return result;
  }
  while (x < y) {
    if (x < y / x) {
      x = x * x;
    } else {
      x = x + 1;
    }
  }
  assert(x != y);
}

