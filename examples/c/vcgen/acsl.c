// ./Cuvee.sh -vcgen -z3 examples/c/vcgen/acsl.c
// expected: valid
// the annotations of ACSL: a contract, whose postcondition refers to \result and \old, a loop invariant and variant
// with chained comparisons, and an assertion
int g;

/*@ requires 0 <= n <= 100;
  @ ensures \result == 2 * n;
  @ ensures g == \old(g) + 1;
  @ assigns g;
  */
int twice(int n) {
  int s = 0;
  g++;
  /*@ loop invariant 0 <= i <= n && s == 2 * i;
    @ loop assigns i, s;
    @ loop variant n - i;
    */
  for (int i = 0; i < n; i++) {
    s += 2;
  }
  return s;
}

int main(void) {
  int r = twice(3);
  //@ assert r == 6 && g == 1;
  return r;
}
