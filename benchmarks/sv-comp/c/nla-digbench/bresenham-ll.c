// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/bresenham-ll.c
// SV-COMP nla-digbench/bresenham-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/bresenham-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int X;
  int Y;
  int x;
  int y;
  int v;
  int xy;
  int yx;
  X = __VERIFIER_nondet_int();
  Y = __VERIFIER_nondet_int();
  v = 2 * Y - X;
  y = 0;
  x = 0;
  while (1 != 0) {
    yx = Y * x;
    xy = X * y;
    assert(2 * yx - 2 * xy - X + 2 * Y - v == 0);
    if (!(x <= X)) {
      break;
    }
    if (v < 0) {
      v = v + 2 * Y;
    } else {
      v = v + 2 * (Y - X);
      y = y + 1;
    }
    x = x + 1;
  }
  xy = x * y;
  yx = Y * x;
  assert(2 * yx - 2 * xy - X + 2 * Y - v + 2 * y == 0);
  result = 0;
  return result;
}

