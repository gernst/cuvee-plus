// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (the sum of a range is not invariant under rotation); the result of rangesum is the logic function fold of the axiomatic Fold
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "rangesum60.c", 18, __extension__ __PRETTY_FUNCTION__); })); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

/*@ requires 60 >= 1;
    assigns x[0..60-1]; */
void init_nondet(int x[60]) {
  int i;
  /*@ loop invariant 0 <= i <= 60;
      loop assigns i, x[0..60-1]; */
  for (i = 0; i < 60; i++) {
    x[i] = __VERIFIER_nondet_int();
  }
}

/*@ axiomatic Fold {
  logic integer fold(int *x, integer n);
  axiom fold_base: \forall int *x; fold(x, 0) == 0;
  axiom fold_step: \forall int *x, integer n; n > 0 ==> fold(x, n) == fold(x, n-1) + (n-1 > 60/2 ? x[n-1] : 0);
} */
/*@ requires 60 >= 1;
    assigns \nothing;
    ensures \result == (int) (60 - 60/2 - 1 > 0 ? fold(x, 60) / (60 - 60/2 - 1) : 0); */
int rangesum (int x[60])
{
  int i;
  long long ret;
  ret = 0;
  int cnt = 0;
  /*@ loop invariant 0 <= i <= 60;
      loop invariant ret == fold(x, i);
      loop invariant cnt == (i > 60/2 + 1 ? i - 60/2 - 1 : 0);
      loop assigns i, ret; */
  for (i = 0; i < 60; i++) {
    if( i > 60/2){
       ret = ret + x[i];
       cnt = cnt + 1;
    }
  }
  if ( cnt !=0)
    return ret / cnt;
  else
    return 0;
}

int main ()
{
  int x[60];
  init_nondet(x);
  int temp;
  int ret;
  int ret2;
  int ret5;

  ret = rangesum(x);

  temp=x[0];x[0] = x[1]; x[1] = temp;
  ret2 = rangesum(x);
  temp=x[0];
  /*@ loop invariant 0 <= i <= 60-1;
      loop invariant \forall integer k; 0 <= k < i ==> x[k] == \at(x[k+1], LoopEntry);
      loop invariant \forall integer k; i <= k < 60 ==> x[k] == \at(x[k], LoopEntry);
      loop invariant temp == \at(x[0], LoopEntry);
      loop assigns i, x[0..60-2]; */
  for(int i =0 ; i<60 -1; i++){
     x[i] = x[i+1];
  }
  x[60 -1] = temp;
  ret5 = rangesum(x);

  if(ret != ret2 || ret !=ret5){
    {reach_error();}
  }
  return 1;
}
