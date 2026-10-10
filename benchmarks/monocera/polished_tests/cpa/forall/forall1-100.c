
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
      int t = i * i;
      arr[i] = t * t;
      i++;
  }
  // assert \forall int j; ((0 <= j) && (j < N)) ==> (arr[j] == (j*j*j*j));

  for (int j = 0; j < N; j++) {
    __VERIFIER_assert(arr[j] == (j*j*j*j));
  }

  return 0;
}
