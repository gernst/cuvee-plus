// ./Cuvee.sh examples/c/printing/readonly.c
// a pointer parameter that is indexed but neither assigned nor written through is an array, a value, which the
// caller passes; other pointer parameters are values of type Ptr
int first(int *a, int n) {
  if (n > 0) return a[0];
  return 0;
}
int main(void) {
  int b[10];
  b[0] = 3;
  return first(b, 10);
}
