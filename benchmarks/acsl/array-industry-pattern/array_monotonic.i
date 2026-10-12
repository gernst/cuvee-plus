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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "array_monotonic.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
int main()
{
 int i;
 int a[100000];
 int b[100000];
 /*@ loop invariant 0 <= i <= 100000;
     loop invariant i % 2 == 0;
     loop invariant \forall integer t; 0 <= t < i ==> (t % 2 == 0 && a[t] == 10) ==> b[t] == 20;
     loop assigns i, b[0..99999]; */
 for(i = 0; i < 100000; i = i + 2)
 {
  a[i] = __VERIFIER_nondet_int();
  if(a[i] == 10)
   b[i] = 20;
 }
 /*@ loop invariant 0 <= i <= 100000;
     loop invariant i % 2 == 0;
     loop invariant \forall integer t; 0 <= t < 100000 ==> (t % 2 == 0 && a[t] == 10) ==> b[t] == 20;
     loop assigns i; */
 for(i = 0; i < 100000; i = i + 2)
 {
  if(a[i] == 10)
   __VERIFIER_assert(b[i] == 20);
 }
}
