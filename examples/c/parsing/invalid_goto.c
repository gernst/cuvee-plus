// ./Cuvee.sh -quiet examples/c/parsing/invalid_goto.c
// a goto whose label marks a statement that falls through is not supported, e.g. those of state machines
int main(void) {
  int x = 0;
  goto L;
  x = 1;
L:
  x = x + 1;
  return x;
}
