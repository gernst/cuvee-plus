// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/trex03-2.c
// SV-COMP loops/trex03-2.yml, translated from benchmarks/sv-comp/dafny/loops/trex03-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  _Bool tmp_4;
  _Bool tmp_5;
  int x1;
  int x2;
  int x3;
  int d1;
  int d2;
  int d3;
  _Bool c1;
  _Bool c2;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  x1 = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_2);
  x2 = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_3);
  x3 = tmp_3;
  d1 = 1;
  d2 = 1;
  d3 = 1;
  tmp_4 = __VERIFIER_nondet_bool();
  c1 = tmp_4;
  tmp_5 = __VERIFIER_nondet_bool();
  c2 = tmp_5;
  while (x1 > 0 && x2 > 0 && x3 > 0) {
    if (c1) {
      x1 = x1 - d1;
    } else if (c2) {
      x2 = x2 - d2;
    } else {
      x3 = x3 - d3;
    }
    c1 = __VERIFIER_nondet_bool();
    c2 = __VERIFIER_nondet_bool();
  }
  assert(x1 == 0 || x2 == 0 || x3 == 0);
  result = 0;
  return result;
}

