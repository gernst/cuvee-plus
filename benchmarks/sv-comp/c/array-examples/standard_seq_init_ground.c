// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-examples/standard_seq_init_ground.c
// SV-COMP array-examples/standard_seq_init_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_seq_init_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int i;
  int x;
  __VERIFIER_assume(0 < N);
  i = 1;
  a[0] = 7;
  while (i < N) {
    a[i] = a[i - 1] + 1;
    i = i + 1;
  }
  x = 1;
  while (x < N) {
    assert(a[x] >= a[x - 1]);
    x = x + 1;
  }
}

