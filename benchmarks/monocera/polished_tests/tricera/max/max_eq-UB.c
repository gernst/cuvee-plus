#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  
  int N = __VERIFIER_nondet_int();
  assume(N > 0);
  

  int arr[N];
  int i = 0;
  while (i < N) {
      arr[i] = i;
      i++;
  }
  

  int max = arr[0];
  for (int i = 0; i < N; i++) {
      if (arr[i] > max) {
          max = arr[i];
      }
  }
  assert(max == N-1);
// assert(\max(arr, 0, N) == N-1);
  return 0;
}
