#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  int N = 100;
  int arr[N];
  int i = 0;
  while (i < N) {
      arr[i] = 2;
      i++;
  }
  i = 0;
  while (i < N) {
      arr[i] = 4;
      i++;
  }
  assert(\sum(arr, 0, N) == 4*N);
  return 0;
}
