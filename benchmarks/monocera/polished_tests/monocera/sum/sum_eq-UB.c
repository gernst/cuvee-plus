#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  
  int N = __VERIFIER_nondet_int();
  __VERIFIER_assume(N > 0);
  
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
