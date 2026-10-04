// expected: valid
// initialized global variables, whose values hold at the entry of main

int counter = 2;
int limit = counter + 3;

int main(void)
{
  assert(counter < limit);
  counter = counter + 1;
  assert(counter == 3);
  return 0;
}
