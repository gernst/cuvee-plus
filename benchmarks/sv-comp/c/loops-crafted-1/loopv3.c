// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/loopv3.c
// SV-COMP loops-crafted-1/loopv3.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/loopv3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int SIZE;

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  SIZE = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < SIZE);
  i = 0;
  j = 0;
  while (i < SIZE) {
    tmp_1 = __VERIFIER_nondet_int();
    if (tmp_1 != 0) {
      i = i + 8;
    } else {
      i = i + 4;
    }
  }
  j = i / 4;
  assert(j * 4 == i);
  result = 0;
  return result;
}

