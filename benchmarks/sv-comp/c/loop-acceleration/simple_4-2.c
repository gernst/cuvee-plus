// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_4-2.c
// SV-COMP loop-acceleration/simple_4-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_4-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  x = 268435440;
  while (x > 0) {
    x = x - 2;
  }
  assert(x % 2 == 0);
}

