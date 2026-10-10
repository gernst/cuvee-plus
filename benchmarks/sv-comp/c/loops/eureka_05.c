// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/eureka_05.c
// SV-COMP loops/eureka_05.yml, translated from benchmarks/sv-comp/dafny/loops/eureka_05.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int Array[];
  int n;
  int N;
  int array_1[];
  int i;
  int lh;
  int rh;
  int j;
  int temp;
  __VERIFIER_assume(0 < N);
  n = N;
  i = N - 1;
  while (i >= 0) {
    array_1[i] = i;
    i = i - 1;
  }
  lh = 0;
  while (lh < n) {
    rh = lh;
    j = lh + 1;
    while (j < n) {
      if (Array[j] < Array[rh]) {
        rh = j;
      }
      j = j + 1;
    }
    temp = Array[lh];
    Array[lh] = Array[rh];
    Array[rh] = temp;
    lh = lh + 1;
  }
  i = 0;
  while (i < N) {
    assert(array_1[i] == i);
    i = i + 1;
  }
}

