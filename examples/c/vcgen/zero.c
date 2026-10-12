// ./Cuvee.sh -vcgen -z3 examples/c/vcgen/zero.c
// expected: valid
// global variables without initializer are zero, as in C
int counter;
_Bool flag;
int a[10];
int main(void)
{
  assert(counter == 0 && !flag && a[3] == 0);
  return 0;
}
