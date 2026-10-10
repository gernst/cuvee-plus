#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  int N = 10;

  int arr[N];
  int i = 0;
  while (i < N) {
    int t = i;
    if (t < 1000) {t = 1000;}
    arr[i] = t;
    i++;
  }
  assert(\min(arr, 0, N) >= 1000);
  return 0;
}
