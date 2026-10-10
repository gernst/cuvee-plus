// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-crafted/mapsum1.c
// SV-COMP array-crafted/mapsum1.yml, translated from benchmarks/sv-comp/dafny/array-crafted/mapsum1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int v;
  int temp;
  int ret;
  int ret2;
  int ret5;
  int x[];
  __VERIFIER_assume(1 < N);
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    x[i] = v;
    i = i + 1;
  }
  ret = 0;
  i = 0;
  while (i < N) {
    ret = ret + i + x[i];
    i = i + 1;
  }
  temp = x[0];
  x[0] = x[1];
  x[1] = temp;
  ret2 = 0;
  i = 0;
  while (i < N) {
    ret2 = ret2 + i + x[i];
    i = i + 1;
  }
  temp = x[0];
  i = 0;
  while (i < N - 1) {
    x[i] = x[i + 1];
    i = i + 1;
  }
  x[N - 1] = temp;
  ret5 = 0;
  i = 0;
  while (i < N) {
    ret5 = ret5 + i + x[i];
    i = i + 1;
  }
  assert(ret == ret2 && ret == ret5);
}

