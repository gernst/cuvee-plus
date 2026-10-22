// ./Cuvee.sh -quiet examples/c/parsing/invalid_switch.c
// a break nested inside the statements of a case is not supported, since the copies of the cases end at breaks
// between their statements only
int main(void) {
  int x = 2, y = 0;
  switch (x) {
    case 1:
      if (y == 0) break;
      y = 1;
  }
  return y;
}
