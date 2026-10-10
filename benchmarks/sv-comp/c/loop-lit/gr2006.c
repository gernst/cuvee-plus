// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/gr2006.c
// SV-COMP loop-lit/gr2006.yml, translated from benchmarks/sv-comp/dafny/loop-lit/gr2006.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int y;
  x = 0;
  y = 0;
  while (true) {
    if (x < 50) {
      y = y + 1;
    } else {
      y = y - 1;
    }
    if (y < 0) {
      break;
    }
    x = x + 1;
  }
  assert(x == 100);
}

