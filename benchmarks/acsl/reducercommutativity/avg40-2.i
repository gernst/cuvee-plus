// ACSL annotations added by hand (benchmarks/acsl/README.md): the result of avg is the logic function fold of the axiomatic Fold, invariant under the swap and the rotation by the lemmas fold_swap and fold_rotate (two arrays instead of labels)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

/*@ requires \false;
    assigns \nothing; */
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "avg40-2.c", 18, __extension__ __PRETTY_FUNCTION__); })); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

/*@ axiomatic Fold {
  logic integer fold(int *x, integer n);
  axiom fold_base: \forall int *x; fold(x, 0) == 0;
  axiom fold_step: \forall int *x, integer n; n > 0 ==> fold(x, n) == fold(x, n-1) + x[n-1];
  lemma fold_swap: \forall int *x1, int *x2, integer n; n >= 2 && x2[0] == x1[1] && x2[1] == x1[0]
    && (\forall integer k; 2 <= k < n ==> x2[k] == x1[k]) ==> fold(x2, n) == fold(x1, n);
  lemma fold_rotate: \forall int *x1, int *x2, integer n; n >= 1 && (\forall integer k; 0 <= k < n-1 ==> x2[k] == x1[k+1])
    && x2[n-1] == x1[0] ==> fold(x2, n) == fold(x1, n);
} */
/*@ requires 40 >= 1;
    assigns \nothing;
    ensures \result == (int) (fold(x, 40) / 40); */
int avg (int x[40])
{
  int i;
  long long ret;
  ret = 0;
  /*@ loop invariant 0 <= i <= 40;
      loop invariant ret == fold(x, i);
      loop assigns i, ret; */
  for (i = 0; i < 40; i++) {
    ret = ret + x[i];
  }
  return ret / 40;
}

int main ()
{
  int x[40];
  int temp;
  int ret;
  int ret2;
  int ret5;

  /*@ loop invariant 0 <= i <= 40;
      loop assigns i, x[0..40-1]; */
  for (int i = 0; i < 40; i++) {
    x[i] = __VERIFIER_nondet_int();
  }

  ret = avg(x);

  temp=x[0];x[0] = x[1]; x[1] = temp;
  ret2 = avg(x);
  temp=x[0];
  /*@ loop invariant 0 <= i <= 40-1;
      loop invariant \forall integer k; 0 <= k < i ==> x[k] == \at(x[k+1], LoopEntry);
      loop invariant \forall integer k; i <= k < 40 ==> x[k] == \at(x[k], LoopEntry);
      loop invariant temp == \at(x[0], LoopEntry);
      loop assigns i, x[0..40-2]; */
  for(int i =0 ; i<40 -1; i++){
     x[i] = x[i+1];
  }
  x[40 -1] = temp;
  ret5 = avg(x);

  if(ret != ret2 || ret !=ret5){
    {reach_error();}
  }
  return 1;
}
