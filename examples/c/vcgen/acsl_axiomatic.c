// ./Cuvee.sh -vcgen -z3 examples/c/vcgen/acsl_axiomatic.c
// an axiomatic of ACSL: a logic function, axioms, which are assumed, and a lemma, which is trusted (free), with
// the step of the recursion backwards, sum(a, n) in terms of sum(a, n-1), whose instances z3 finds; a logic function
// and a predicate with bodies, and pointers in logic signatures and quantifiers, which are arrays
/*@ axiomatic Sum {
  logic integer sum(int *a, integer n) reads a[0..n-1];
  axiom sum_zero: \forall int *a; sum(a, 0) == 0;
  axiom sum_step: \forall int *a, integer n; n > 0 ==> sum(a, n) == sum(a, n-1) + a[n-1];
  lemma sum_nonneg: \forall int *a, integer n; n >= 0 && (\forall integer k; 0 <= k < n ==> a[k] >= 0) ==> sum(a, n) >= 0;
} */
/*@ logic integer twice(integer x) = 2 * x; */
/*@ predicate small(integer x) = x < 100; */
/*@ requires n >= 0;
    ensures \result == sum(a, n); */
int total(int a[], int n) {
  int s = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant s == sum(a, i); */
  for (int i = 0; i < n; i++) s += a[i];
  return s;
}
int main(void) { int a[3]; a[0] = 1; a[1] = 2; a[2] = 3; int t = total(a, 3); //@ assert t == sum(a, 3) && twice(3) == 6 && small(t);
  return 0; }
