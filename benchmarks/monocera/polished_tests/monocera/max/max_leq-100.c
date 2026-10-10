#include <assert.h>

extern int __VERIFIER_nondet_int();

int main() {
  int N = 100;

  int arr[N];
  int i = 0;
  while (i < N) {
    int t = i;
    if (t > 10000) {t = 10000;}
    arr[i] = t;
    i++;
  }
  assert(\max(arr, 0, N) <= 10000);
  return 0;
}
