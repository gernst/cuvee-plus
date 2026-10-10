// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/array-2.c
// SV-COMP loops/array-2.yml, translated from benchmarks/sv-comp/dafny/loops/array-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int SIZE;
  int j;
  int k;
  int Array[];
  int menor;
  SIZE = 1;
  menor = __VERIFIER_nondet_int();
  j = 0;
  while (j < SIZE) {
    tmp_1 = __VERIFIER_nondet_int();
    Array[j] = tmp_1;
    if (Array[j] <= menor) {
      menor = Array[j];
    }
    j = j + 1;
  }
  assert(Array[0] > menor);
  result = 0;
  return result;
}

