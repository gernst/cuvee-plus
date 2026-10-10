// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/trex01-1.c
// SV-COMP loops/trex01-1.yml, translated from benchmarks/sv-comp/dafny/loops/trex01-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void f(int d) {
  int tmp_1;
  int tmp_2;
  int tmp_3;
  _Bool tmp_4;
  _Bool tmp_5;
  int x;
  int y;
  int k;
  int z;
  _Bool c;
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  y = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  k = tmp_3;
  z = 1;
  while (z < k) {
    z = 2 * z;
  }
  assert(z >= 2);
  while (x > 0 && y > 0) {
    tmp_4 = __VERIFIER_nondet_bool();
    c = tmp_4;
    if (c) {
      x = x - d;
      tmp_5 = __VERIFIER_nondet_bool();
      y = tmp_5 ? 1 : 0;
      z = z - 1;
    } else {
      y = y - d;
    }
  }
}

int main(void) {
  int result;
  _Bool tmp_6;
  _Bool c;
  tmp_6 = __VERIFIER_nondet_bool();
  c = tmp_6;
  if (c) {
    f(1);
  } else {
    f(2);
  }
  result = 0;
  return result;
}

