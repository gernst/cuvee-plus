// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-examples/standard_password_ground.c
// SV-COMP array-examples/standard_password_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_password_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int x;
  int v;
  int result;
  int password[];
  int guess[];
  __VERIFIER_assume(0 < N);
  result = 1;
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    password[i] = v;
    v = __VERIFIER_nondet_int();
    guess[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (password[i] != guess[i]) {
      result = 0;
    }
    i = i + 1;
  }
  if (result != 0) {
    x = 0;
    while (x < N) {
      assert(password[x] == guess[x]);
      x = x + 1;
    }
  }
}

