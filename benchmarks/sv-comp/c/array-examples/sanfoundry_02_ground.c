// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sanfoundry_02_ground.c
// SV-COMP array-examples/sanfoundry_02_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/sanfoundry_02_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int x;
  int v;
  int largest1;
  int largest2;
  int temp;
  int Array[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    Array[i] = v;
    i = i + 1;
  }
  largest1 = Array[0];
  largest2 = Array[1];
  if (largest1 < largest2) {
    temp = largest1;
    largest1 = largest2;
    largest2 = temp;
  }
  i = 2;
  while (i < N) {
    if (Array[i] >= largest1) {
      largest2 = largest1;
      largest1 = Array[i];
    } else if (Array[i] > largest2) {
      largest2 = Array[i];
    }
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(Array[x] <= largest1);
    x = x + 1;
  }
  x = 0;
  while (x < N) {
    assert(Array[x] <= largest2 || Array[x] == largest1);
    x = x + 1;
  }
}

