#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  int N = 10;

  int arr[N];
  int i = 0;
  while (i < N) {
      arr[i] = i;
      i++;
  }
  assert(\max(arr, 0, N) == N-1);
  return 0;
}
