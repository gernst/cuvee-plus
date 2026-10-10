// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/insertion_sort-1-2.c
// SV-COMP loops/insertion_sort-1-2.yml, translated from benchmarks/sv-comp/dafny/loops/insertion_sort-1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int SIZE;
  int i;
  int j;
  int k;
  int key;
  int v[];
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  SIZE = tmp_1;
  if (SIZE >= 1000000000) {
    result = 0;
    return result;
  }
  j = 0;
  while (j < SIZE) {
    tmp_2 = __VERIFIER_nondet_int();
    v[j] = tmp_2;
    j = j + 1;
  }
  j = 1;
  while (j < SIZE) {
    key = v[j];
    i = j - 1;
    while (i >= 0 && v[i] > key) {
      if (i < 2) {
        v[i + 1] = v[i];
      }
      i = i - 1;
    }
    v[i + 1] = key;
    j = j + 1;
  }
  k = 1;
  while (k < SIZE) {
    assert(v[k - 1] <= v[k]);
    k = k + 1;
  }
  result = 0;
  return result;
}

