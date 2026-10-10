// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/phases_2-2.c
// SV-COMP loop-acceleration/phases_2-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/phases_2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int y;
  x = 1;
  y = __VERIFIER_nondet_int();
  __VERIFIER_assume(y >= 0);
  if (!(y > 0)) {
    return;
  }
  while (x < y) {
    if (x < y / x) {
      x = x * x;
    } else {
      x = x + 1;
    }
  }
  assert(x == y);
}

