// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_partition_original_ground.c
// SV-COMP array-examples/standard_partition_original_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_partition_original_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a;
  int b;
  int c;
  int x;
  int v;
  int aa[];
  int bb[];
  int cc[];
  __VERIFIER_assume(0 < N);
  a = 0;
  b = 0;
  c = 0;
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    aa[i] = v;
    i = i + 1;
  }
  while (a < N) {
    if (aa[a] >= 0) {
      bb[b] = aa[a];
      b = b + 1;
    } else {
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
}

