// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/while_infinite_loop_4.c
// SV-COMP loops/while_infinite_loop_4.yml, translated from benchmarks/sv-comp/dafny/loops/while_infinite_loop_4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int x;

void eval(void) {
  while (1 != 0) {
    x = 1;
    break;
  }
  return;
}

int main(void) {
  int result;
  x = 0;
  while (1 != 0) {
    eval();
    assert(x == 0);
  }
  assert(x == 0);
  result = 0;
  return result;
}

