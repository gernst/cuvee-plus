// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/mine2017-ex4.6.c
// SV-COMP loop-lit/mine2017-ex4.6.yml, translated from benchmarks/sv-comp/dafny/loop-lit/mine2017-ex4.6.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  x = 40;
  while (x != 0) {
    assert(x <= 40);
    x = x - 1;
    assert(x >= 0);
  }
  assert(x == 0);
}

