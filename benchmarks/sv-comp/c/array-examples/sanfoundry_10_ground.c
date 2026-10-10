// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sanfoundry_10_ground.c
// SV-COMP array-examples/sanfoundry_10_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/sanfoundry_10_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int x;
  int v;
  int n;
  int pos;
  int element;
  int found;
  int vectorx[];
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < n);
  element = __VERIFIER_nondet_int();
  found = 0;
  i = 0;
  while (i < n) {
    v = __VERIFIER_nondet_int();
    vectorx[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < n && found == 0) {
    if (vectorx[i] == element) {
      found = 1;
      pos = i;
    }
    i = i + 1;
  }
  if (found != 0) {
    i = pos;
    while (i < n - 1) {
      vectorx[i] = vectorx[i + 1];
      i = i + 1;
    }
  }
  if (found != 0) {
    x = 0;
    while (x < pos) {
      assert(vectorx[x] != element);
      x = x + 1;
    }
  }
}

