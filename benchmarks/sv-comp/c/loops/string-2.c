// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/string-2.c
// SV-COMP loops/string-2.yml, translated from benchmarks/sv-comp/dafny/loops/string-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int tmp_2;
  int string_A[];
  int string_B[];
  int i;
  int j;
  int nc_A;
  int nc_B;
  int found;
  __VERIFIER_assume(0 < N);
  found = 0;
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    string_A[i] = tmp_1;
    i = i + 1;
  }
  if (string_A[N - 1] != 0) {
    result = 0;
    return result;
  }
  i = 0;
  while (i < N) {
    tmp_2 = __VERIFIER_nondet_int();
    string_B[i] = tmp_2;
    i = i + 1;
  }
  if (string_B[N - 1] != 0) {
    result = 0;
    return result;
  }
  nc_A = 0;
  while (string_A[nc_A] != 0) {
    nc_A = nc_A + 1;
  }
  nc_B = 0;
  while (string_B[nc_B] != 0) {
    nc_B = nc_B + 1;
  }
  if (!(nc_B >= nc_A)) {
    result = 0;
    return result;
  }
  j = 0;
  i = j;
  while (i < nc_A && j < nc_B) {
    if (string_A[i] == string_B[j]) {
      i = i + 1;
      j = j + 1;
    } else {
      i = i - j + 1;
      j = 0;
    }
  }
  found = (j > nc_B - 1 ? 1 : 0) << i;
  assert(found == 0 || found == 1);
  result = 0;
  return result;
}

