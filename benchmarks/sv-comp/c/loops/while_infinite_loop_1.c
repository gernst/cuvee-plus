// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/while_infinite_loop_1.c
// SV-COMP loops/while_infinite_loop_1.yml, translated from benchmarks/sv-comp/dafny/loops/while_infinite_loop_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  x = 0;
  while (1 != 0) {
    assert(x == 0);
  }
  assert(x != 0);
}

