// ./Cuvee.sh examples/c/printing/annotations.c
// annotations of ACSL: contracts, loop invariants and variants, and assertions that are not C, with \result, \old,
// quantifiers, implications, and equivalences; chained comparisons are conjunctions; the precondition of main that the
// global variables are zero is implicit
int g;
int b[10];

/*@ requires 0 <= n <= 10;
  @ ensures \result == \old(g) + n;
  @ ensures \forall integer k; 0 <= k < n ==> b[k] == k;
  @ assigns g, b[0..n-1];
  */
int fill(int n) {
  int old = g;
  /*@ loop invariant 0 <= i <= n && g == old + i;
    @ loop invariant \forall integer k; 0 <= k < i ==> b[k] == k;
    */
  for (int i = 0; i < n; i++) {
    b[i] = i;
    g = g + 1;
  }
  return g;
}

/*@ requires g == 0; */
int main(void) {
  _Bool p = g == 0;
  int r = fill(3);
  int j = 5;
  //@ loop variant j;
  while (j > 0) j--;
  //@ assert (p <==> r == 3) && (\exists integer k; b[k] == 2);
  //@ assert \forall boolean q; q || !q;
  //@ assert (unsigned char) (r + 255) == 2;
  return r;
}
