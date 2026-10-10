// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_partition_ground-1.c
// SV-COMP array-examples/standard_partition_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_partition_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int aa[];
  int a;
  int b;
  int c;
  int bb[];
  int cc[];
  int x;
  __VERIFIER_assume(0 < N);
  a = 0;
  b = 0;
  c = 0;
  while (a < N) {
    tmp_1 = __VERIFIER_nondet_int();
    aa[a] = tmp_1;
    if (aa[a] >= 0) {
      bb[b] = aa[a];
      b = b + 1;
    }
    a = a + 1;
  }
  a = 0;
  while (a < N) {
    if (aa[a] >= 0) {
      cc[c] = aa[a];
      c = c + 1;
    }
    a = a + 1;
  }
  x = 0;
  while (x < b) {
    assert(bb[x] >= 0);
    x = x + 1;
  }
  x = 0;
  while (x < c) {
    assert(cc[x] < 0);
    x = x + 1;
  }
  result = 0;
  return result;
}

