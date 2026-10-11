// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sanfoundry_02_ground.c
// SV-COMP array-examples/sanfoundry_02_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/sanfoundry_02_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sanfoundry_02_ground.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int N = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  int largest1 = __VERIFIER_nondet_int();
  int largest2 = __VERIFIER_nondet_int();
  int temp = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int Array[N];
  assume_abort_if_not(0 < N);
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
    __VERIFIER_assert(Array[x] <= largest1);
    x = x + 1;
  }
  x = 0;
  while (x < N) {
    __VERIFIER_assert(Array[x] <= largest2 || Array[x] == largest1);
    x = x + 1;
  }
}

