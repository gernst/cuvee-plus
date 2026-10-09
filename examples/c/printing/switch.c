// ./Cuvee.sh examples/c/printing/switch.c
// a switch is a chain of conditionals over the value of its test, where each case is followed by copies of the
// statements of the cases it falls through to, up to the first break, and default comes last
int main(void) {
  int x = 2, y = 0;
  switch (x + 1) {
    case 1:
      y = 1;
      break;
    case 2:
    case 3:
      y = y + 2;
    case 4:
      y = y + 4;
      break;
    default:
      y = 8;
  }
  return y;
}
