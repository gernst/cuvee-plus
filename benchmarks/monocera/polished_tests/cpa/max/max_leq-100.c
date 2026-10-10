
void reach_error(){};

void __VERIFIER_assume(int cond) {
  if (!cond) {
    while (1) {};
  }
}

void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}
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
  

  int max = arr[0];
  for (int i = 0; i < N; i++) {
      if (arr[i] > max) {
          max = arr[i];
      }
  }
  __VERIFIER_assert(max <= 10000);
// __VERIFIER_assert(\max(arr, 0, N) <= 10000);
  return 0;
}
