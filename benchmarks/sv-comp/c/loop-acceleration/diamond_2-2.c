// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/diamond_2-2.c
// SV-COMP loop-acceleration/diamond_2-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/diamond_2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  x = 0;
  y = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= y);
  while (x < N) {
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + 1;
    }
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + -2;
    }
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + 2;
    }
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + -2;
    }
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + 2;
    }
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + -4;
    }
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + 4;
    }
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + 2;
    }
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + -4;
    }
    if (y % 2 == 0) {
      x = x + 2;
    } else {
      x = x + -4;
    }
  }
  assert(x % 2 == y % 2);
}

