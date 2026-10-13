// ./Cuvee.sh -teq -prove -split -prove -fallback examples/c/teq/fallback.c
// the loop of SV-COMP nla-digbench/bresenham-ll: the flags v < 0 become a combinator that is not equated to a variable,
// a dependency of the trace of y, which is a fresh function, whose arguments include the length n of the counter
int main() {
  int X; int Y; int x; int y; int v;
  v = 2 * Y - X; y = 0; x = 0;
  while (1) {
    assert(2 * Y * x - 2 * X * y - X + 2 * Y - v == 0);
    if (!(x <= X)) break;
    if (v < 0) { v = v + 2 * Y; } else { v = v + 2 * (Y - X); y++; }
    x++;
  }
  return 0;
}
