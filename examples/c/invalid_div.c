// ./Cuvee.sh examples/c/invalid_div.c
// expected: invalid
// division truncates towards zero in C, -7 / 2 is -3, unlike div of SMT-LIB, which rounds down to -4

int main(void)
{
  int x = -7;
  assert(x / 2 == -4);
  return 0;
}
