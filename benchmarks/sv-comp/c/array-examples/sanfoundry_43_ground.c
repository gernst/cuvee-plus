// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sanfoundry_43_ground.c
// SV-COMP array-examples/sanfoundry_43_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/sanfoundry_43_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void incrementArray(int src[], int dst[], int N) {
  int dst_1[];
  int i;
  dst_1 = dst;
  i = 0;
  while (i < N) {
    dst_1[i] = src[i] + 1;
    i = i + 1;
  }
}

int main(void) {
  int result;
  int N;
  int tmp_2;
  int src[];
  int dst[];
  int x;
  int i;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp_2 = __VERIFIER_nondet_int();
    src[i] = tmp_2;
    i = i + 1;
  }
  incrementArray(src, dst, N);
  x = 0;
  while (x < N) {
    src[x] = dst[x] - 1;
    x = x + 1;
  }
  result = 0;
  return result;
}

