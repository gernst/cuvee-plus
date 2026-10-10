
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
      arr[i] = 2;
      i++;
  }
  i = 0;
  while (i < N) {
      arr[i] = 4;
      i++;
  }
  

  int sum = 0;
  for (int i = 0; i < N; i++) {
      sum += arr[i];
  }
  __VERIFIER_assert(sum == 4*N);
// __VERIFIER_assert(\sum(arr, 0, N) == 4*N);
  return 0;
}
