// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/linear_sea.ch.c
// SV-COMP loops/linear_sea.ch.yml, translated from benchmarks/sv-comp/dafny/loops/linear_sea.ch.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int SIZE;

int linear_search(int a[], int n, int q) {
  int result;
  int j;
  j = 0;
  while (j < n && a[j] != q) {
    j = j + 1;
  }
  if (j < SIZE) {
    result = 1;
    return result;
  } else {
    result = 0;
    return result;
  }
}

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int a[];
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  SIZE = tmp_1 / 8 + 1;
  if (SIZE > 1) {
    a[SIZE / 2] = 3;
    tmp_2 = linear_search(a, SIZE, 3);
    assert(tmp_2 != 0);
  }
}

