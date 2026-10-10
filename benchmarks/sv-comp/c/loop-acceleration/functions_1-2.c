// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/functions_1-2.c
// SV-COMP loop-acceleration/functions_1-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/functions_1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int f(int z) {
  int result;
  result = z + 2;
  return result;
}

int main(void) {
  int result;
  int N;
  int x;
  __VERIFIER_assume(0 < N);
  x = 0;
  while (x < N) {
    x = f(x);
  }
  assert(x % 2 != 0);
}

