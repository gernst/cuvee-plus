// ACSL annotations added by hand (benchmarks/acsl/README.md)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "partial_lesser_bound-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int a[10000000];
int i;
int main()
{
 /*@ loop invariant 0 <= i <= 10000000;
     loop invariant \forall integer t; 0 <= t < i ==> a[t] == 0;
     loop assigns i, a[0..9999999]; */
 for(i=0;i<10000000;i++)
 {
 a[i] = 0 ;
 }
 /*@ loop invariant 0 <= i <= 5000000;
     loop invariant \forall integer t; 0 <= t < i ==> a[t] == 10;
     loop assigns i, a[0..4999999]; */
 for(i=0;i<10000000/2;i++)
 {
 a[i] = 10 ;
 }
 /*@ loop invariant 0 <= i <= 5000000;
     loop invariant \forall integer t; 0 <= t < 5000000 ==> a[t] == 10;
     loop assigns i; */
 for(i=0;i<10000000/2;i++)
 {
  __VERIFIER_assert(a[i]==10);
 }
 return 0;
}
