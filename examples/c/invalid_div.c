// expected: valid
// division is translated to div of SMT-LIB (see TODO.md), which rounds down, unlike C's /

int main(void)
{
  int x = -7;
  assert(x / 2 == -4);
  return 0;
}
