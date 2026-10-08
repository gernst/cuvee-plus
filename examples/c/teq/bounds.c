// ./Cuvee.sh -teq -split -simplify examples/c/teq/bounds.c
// the variable of a counter that runs in parallel to the iterations is bounded like them,
// since its value earlier(k, ⌊I⌋) is k within the range of k
int main(void) { int s = 0; int i;
  for (i = 0; i < 10; i++) { if (0 <= i && i < 10) s = s + 1; else s = s + 2; }
  assert(s == 10); return 0; }
