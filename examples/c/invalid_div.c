// expected: invalid
// SMT-LIB's div rounds down for negative numbers, C's / does not

int main(void)
{
  int x = -7;
  assert(x / 2 == -4);
  return 0;
}
