// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/terminator_02-2.c
// SV-COMP loops/terminator_02-2.yml, translated from benchmarks/sv-comp/dafny/loops/terminator_02-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int tmp_2;
  _Bool tmp_3;
  int x;
  int z;
  _Bool tmp;
  __VERIFIER_assume(0 < N);
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  z = tmp_2;
  if (!(x > -N)) {
    result = 0;
    return result;
  }
  if (!(z > N)) {
    result = 0;
    return result;
  }
  while (x < N && z > N) {
    tmp_3 = __VERIFIER_nondet_bool();
    tmp = tmp_3;
    if (tmp) {
      x = x + 1;
    } else {
      x = x - 1;
      z = z - 1;
    }
  }
  assert(x >= N || z <= N);
  result = 0;
  return result;
}

