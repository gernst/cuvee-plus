
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
  
  int N = __VERIFIER_nondet_int();
  __VERIFIER_assume(N > 0);
  

  int arr[N];
  int i = 0;
  while (i < N) {
      arr[i] = i;
      i++;
  }
  

  int min = arr[0];
  for (int i = 0; i < N; i++) {
      if (arr[i] < min) {
          min = arr[i];
      }
  }
  __VERIFIER_assert(min == 0);
// __VERIFIER_assert(\min(arr, 0, N) == 0);
  return 0;
}
