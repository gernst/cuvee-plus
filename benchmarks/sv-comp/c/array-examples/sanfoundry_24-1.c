// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sanfoundry_24-1.c
// SV-COMP array-examples/sanfoundry_24-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/sanfoundry_24-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int num;
  int v;
  int Array[];
  num = __VERIFIER_nondet_int();
  i = 0;
  while (i < num) {
    v = __VERIFIER_nondet_int();
    Array[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < num) {
    if (Array[i] % 2 == 0) {
      assert(Array[i] % 2 == 0);
    }
    i = i + 1;
  }
  i = 0;
  while (i < num) {
    if (Array[i] % 2 != 0) {
      assert(Array[i] % 2 != 0);
    }
    i = i + 1;
  }
}

