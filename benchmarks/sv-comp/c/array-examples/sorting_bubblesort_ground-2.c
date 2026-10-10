// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sorting_bubblesort_ground-2.c
// SV-COMP array-examples/sorting_bubblesort_ground-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/sorting_bubblesort_ground-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int a[];
  int swapped;
  int x;
  int y;
  int j;
  int i;
  int t;
  __VERIFIER_assume(0 < N);
  j = 0;
  while (j < N) {
    tmp_1 = __VERIFIER_nondet_int();
    a[j] = tmp_1;
    j = j + 1;
  }
  swapped = 1;
  while (swapped != 0) {
    swapped = 0;
    i = 1;
    while (i < N) {
      if (a[i - 1] < a[i]) {
        t = a[i];
        a[i] = a[i - 1];
        a[i - 1] = t;
        swapped = 1;
      }
      i = i + 1;
    }
  }
  x = 0;
  while (x < N) {
    y = x + 1;
    while (y < N) {
      assert(a[x] <= a[y]);
      y = y + 1;
    }
    x = x + 1;
  }
  result = 0;
  return result;
}

