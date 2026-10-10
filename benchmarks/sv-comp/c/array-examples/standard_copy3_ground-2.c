// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_copy3_ground-2.c
// SV-COMP array-examples/standard_copy3_ground-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_copy3_ground-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int tmp_2;
  int a1[];
  int a2[];
  int a3[];
  int a4[];
  int a;
  int i;
  int x;
  __VERIFIER_assume(0 < N);
  a = 0;
  while (a < N) {
    tmp_1 = __VERIFIER_nondet_int();
    a1[a] = tmp_1;
    tmp_2 = __VERIFIER_nondet_int();
    a3[a] = tmp_2;
    a = a + 1;
  }
  i = 0;
  while (i < N) {
    a2[i] = a1[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a4[i] = a2[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a4[i] = a3[i];
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(a1[x] == a4[x]);
    x = x + 1;
  }
  result = 0;
  return result;
}

