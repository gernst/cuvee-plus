// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_partition_ground-2.c
// SV-COMP array-examples/standard_partition_ground-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_partition_ground-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int aa[];
  int bb[];
  int cc[];
  int a;
  int b;
  int c;
  int i;
  int x;
  int tmp;
  __VERIFIER_assume(0 < N);
  a = 0;
  b = 0;
  c = 0;
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    aa[i] = tmp;
    i = i + 1;
  }
  while (a < N) {
    if (aa[a] >= 0) {
      bb[b] = aa[a];
      b = b + 1;
    }
    a = a + 1;
  }
  a = 0;
  while (a < N) {
    if (aa[a] < 0) {
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
}

