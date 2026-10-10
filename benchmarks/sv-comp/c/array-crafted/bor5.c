// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-crafted/bor5.c
// SV-COMP array-crafted/bor5.yml, translated from benchmarks/sv-comp/dafny/array-crafted/bor5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int bor(int x[]) {
  int result;
  int i;
  int res;
  res = x[0];
  i = 1;
  while (i < N) {
    res = res | x[i];
    i = i + 1;
  }
  result = res;
  return result;
}

int main(void) {
  int result;
  int tmp_1;
  int x[];
  int temp;
  int ret;
  int ret2;
  int ret5;
  int i;
  N = __VERIFIER_nondet_int();
  if (N > 1) {
    i = 0;
    while (i < N) {
      tmp_1 = __VERIFIER_nondet_int();
      x[i] = tmp_1;
      i = i + 1;
    }
    ret = bor(x);
    temp = x[0];
    x[0] = x[1];
    x[1] = temp;
    ret2 = bor(x);
    temp = x[0];
    i = 0;
    while (i < N - 1) {
      x[i] = x[i + 1];
      i = i + 1;
    }
    x[N - 1] = temp;
    ret5 = bor(x);
    if (ret != ret2 || ret != ret5) {
      assert(false);
    }
  }
  result = 1;
  return result;
}

