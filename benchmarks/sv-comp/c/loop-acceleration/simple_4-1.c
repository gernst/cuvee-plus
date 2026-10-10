// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_4-1.c
// SV-COMP loop-acceleration/simple_4-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_4-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  x = 268435441;
  while (x > 1) {
    x = x - 2;
  }
  assert(!(x % 2 != 0));
}

