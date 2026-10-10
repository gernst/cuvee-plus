// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/trex02-1.c
// SV-COMP loops/trex02-1.yml, translated from benchmarks/sv-comp/dafny/loops/trex02-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int x;

void foo(void) {
  x = x - 1;
}

int main(void) {
  int result;
  _Bool tmp_1;
  _Bool c;
  x = __VERIFIER_nondet_int();
  while (x > 0) {
    tmp_1 = __VERIFIER_nondet_bool();
    c = tmp_1;
    if (c) {
      foo();
    } else {
      foo();
    }
  }
  assert(x <= 0);
}

