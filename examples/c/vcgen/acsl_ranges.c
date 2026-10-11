// ./Cuvee.sh -verify -z3 examples/c/vcgen/acsl_ranges.c
// annotations of ACSL as in Frama-C/WP: the ranges of the unsigned variables that an annotated loop modifies are
// invariants, and those of the unsigned parameters of a function with annotations are preconditions;
// \at(e, LoopEntry) is the value before the loop, \at(e, Pre) at the entry of the function, \valid is true;
// & of truth values is their conjunction
extern unsigned int __VERIFIER_nondet_uint(void);

/*@ requires \valid(a + (0..n-1));
  @ ensures \result == \at(n, Pre);
  */
unsigned int count(int a[], unsigned int n) {
  unsigned int x = n;
  unsigned int y = 0;
  /*@ loop invariant x + y == \at(x, LoopEntry);
    @ loop assigns x, y;
    */
  while (x > 0) {
    x--;
    y++;
  }
  return y;
}

int main(void) {
  int a[10];
  unsigned int n = __VERIFIER_nondet_uint();
  unsigned int r = count(a, n);
  //@ assert (r == n) & (r >= 0);
  return 0;
}
