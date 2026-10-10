#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  int N = 10;
  int arr[N];

  int i = 0;
  while (i < N) {
      arr[i] = -i;
      i++;
  }
  i = 0;
  while (i < N) {
      arr[i] = i;
      i++;
  }
  

  int sum = 0;
  for (int i = 0; i < N; i++) {
      sum += arr[i];
  }
  assert(sum >= 0);
// assert(\sum(arr, 0, N) >= 0);
  return 0;
}
