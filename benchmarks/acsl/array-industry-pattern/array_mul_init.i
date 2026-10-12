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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "array_mul_init.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
short __VERIFIER_nondet_short();
int main()
{
 int a[100000];
 int b[100000];
 int k;
 int i;
 /*@ loop invariant 0 <= i <= 100000;
     loop invariant \forall integer t; 0 <= t < i ==> a[t] == t && b[t] == t;
     loop assigns i, a[0..99999], b[0..99999]; */
 for (i = 0; i<100000 ; i++)
 {
  a[i] = i;
  b[i] = i ;
 }
 /*@ loop invariant 0 <= i <= 100000;
     loop invariant \forall integer t; 0 <= t < i ==> a[t] == b[t] || b[t] == a[t] * a[t];
     loop invariant \forall integer t; i <= t < 100000 ==> a[t] == b[t];
     loop assigns i, a[0..99999], b[0..99999]; */
 for (i=0; i< 100000; i++)
 {
  if(__VERIFIER_nondet_short())
  {
   k = __VERIFIER_nondet_short();
   a[i] = k;
   b[i] = k * k ;
  }
 }
 /*@ loop invariant 0 <= i <= 100000;
     loop invariant \forall integer t; 0 <= t < 100000 ==> a[t] == b[t] || b[t] == a[t] * a[t];
     loop assigns i; */
 for (i=0; i< 100000; i++)
 {
  __VERIFIER_assert(a[i] == b[i] || b[i] == a[i] * a[i]);
 }
}
