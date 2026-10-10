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
  

  int sum = 0;
  for (int i = 0; i < N; i++) {
      sum += arr[i];
  }
  assert(sum == 4*N);
// assert(\sum(arr, 0, N) == 4*N);
  return 0;
}
