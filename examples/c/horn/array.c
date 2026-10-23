// ./Cuvee.sh -chc -prove examples/c/horn/array.c
// expected: valid
// arrays are values, which are copied when passed

void clear(int a[], int n)
{
  for (int i = 0; i < n; i++)
    a[i] = 0;
}

int main(void)
{
  int a[10];
  a[0] = 1;
  clear(a, 10);
  // the array of main is unchanged
  assert(a[0] == 1);
  _Bool b = a[0] > 0;
  do {
    a[0] = a[0] - 1;
  } while (a[0] > 0 && b);
  assert(a[0] == 0);
  return 0;
}
