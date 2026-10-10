#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  
  int N = __VERIFIER_nondet_int();
  assume(N > 0);
  

  int arr[N];
  int i = 0;
  while (i < N) {
    int t = i;
    if (t > 1000) {t = 1000;}
    arr[i] = t;
    i++;
  }
  

  int max = arr[0];
  for (int i = 0; i < N; i++) {
      if (arr[i] > max) {
          max = arr[i];
      }
  }
  assert(max <= 1000);
// assert(\max(arr, 0, N) <= 1000);
  return 0;
}
