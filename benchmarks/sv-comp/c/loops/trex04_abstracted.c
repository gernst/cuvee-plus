// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/trex04_abstracted.c
// SV-COMP loops/trex04_abstracted.yml, translated from benchmarks/sv-comp/dafny/loops/trex04_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void foo(void) {
  _Bool tmp_1;
  _Bool tmp_2;
  int y;
  _Bool c1;
  _Bool c2;
  y = 0;
  tmp_1 = __VERIFIER_nondet_bool();
  c1 = tmp_1;
  tmp_2 = __VERIFIER_nondet_bool();
  c2 = tmp_2;
  if (c1) {
    y = y + 1;
  }
  if (c2) {
    y = y - 1;
  } else {
    y = y + 10;
  }
}

int main(void) {
  int result;
  int tmp_3;
  _Bool tmp_4;
  _Bool tmp_5;
  int d;
  int x;
  _Bool c1;
  _Bool c2;
  d = 1;
  tmp_3 = __VERIFIER_nondet_int();
  x = tmp_3;
  tmp_4 = __VERIFIER_nondet_bool();
  c1 = tmp_4;
  tmp_5 = __VERIFIER_nondet_bool();
  c2 = tmp_5;
  if (c1) {
    d = d - 1;
  }
  if (c2) {
    foo();
  }
  c1 = __VERIFIER_nondet_bool();
  c2 = __VERIFIER_nondet_bool();
  if (c1) {
    foo();
  }
  if (c2) {
    d = d - 1;
  }
  if (x > 0) {
    x = __VERIFIER_nondet_int();
  }
  if (x > 0) {
    __VERIFIER_assume(false);
  }
  assert(x <= 0);
}

