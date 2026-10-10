#include<seahorn/seahorn.h>

#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  int N = 100;

  int arr[N];
  int i = 0;
  while (i < N) {
    int t = i;
    if (t < 10000) {t = 10000;}
    arr[i] = t;
    i++;
  }
  

  int min = arr[0];
  for (int i = 0; i < N; i++) {
      if (arr[i] < min) {
          min = arr[i];
      }
  }
  sassert(min >= 10000);
// sassert(\min(arr, 0, N) >= 10000);
  return 0;
}
