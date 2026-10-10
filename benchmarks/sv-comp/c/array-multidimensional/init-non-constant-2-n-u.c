// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/init-non-constant-2-n-u.c
// SV-COMP array-multidimensional/init-non-constant-2-n-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/init-non-constant-2-n-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  int q;
  int s;
  int A[][];
  int C;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  C = tmp_1;
  q = __VERIFIER_nondet_int();
  s = __VERIFIER_nondet_int();
  i = 0;
  j = 0;
  while (i < q) {
    j = 0;
    while (j < s) {
      A[i][j] = i + j + C;
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < q) {
    j = 0;
    while (j < s) {
      assert(A[i][j] == i + j + C);
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

