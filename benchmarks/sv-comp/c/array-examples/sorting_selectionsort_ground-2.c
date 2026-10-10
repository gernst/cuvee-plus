// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sorting_selectionsort_ground-2.c
// SV-COMP array-examples/sorting_selectionsort_ground-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/sorting_selectionsort_ground-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_2;
  int a[];
  int i;
  int x;
  int y;
  int i_1;
  int k;
  int s;
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  i_1 = 0;
  while (i_1 < N) {
    tmp_2 = __VERIFIER_nondet_int();
    a[i_1] = tmp_2;
    i_1 = i_1 + 1;
  }
  i = 0;
  while (i < N) {
    k = i + 1;
    s = i;
    while (k < N) {
      if (a[k] < a[s]) {
        s = k;
      }
      k = k + 1;
    }
    if (s != i) {
      tmp = a[s];
      a[s] = a[i];
      a[i] = tmp;
    }
    x = 0;
    while (x < i) {
      y = x + 1;
      while (y < i) {
        assert(a[x] <= a[y]);
        y = y + 1;
      }
      x = x + 1;
    }
    x = i;
    while (x < N) {
      assert(a[x] >= a[i]);
      x = x + 1;
    }
    i = i + 1;
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

