// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sorting_selectionsort_2_ground.c
// SV-COMP array-examples/sorting_selectionsort_2_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/sorting_selectionsort_2_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int a[];
  int i;
  int x;
  int y;
  int k;
  int s;
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    a[i] = tmp_1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    k = i;
    s = i + 1;
    while (k < N) {
      if (a[k] > a[s]) {
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
    x = i + 1;
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

