// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (c[15000] is not written when q != 0)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "array_single_elem_init.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
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
 int c[100000];
 /*@ loop invariant 0 <= i <= 100000;
     loop invariant \forall integer t; 0 <= t < i ==> (a[t] == 0 || a[t] == 1) && (a[t] != 0 ==> b[t] == t % 2 && c[t] == (t % 2 == 0 ? 0 : 1));
     loop assigns i, a[0..99999], b[0..99999], c[0..99999]; */
 for (i = 0; i < 100000; i++)
 {
  int q = __VERIFIER_nondet_int();
  a[i] = 0;
  if (q == 0)
  {
   a[i] = 1;
   b[i] = i % 2;
  }
  if (a[i] != 0)
  {
   if (b[i] == 0)
   {
    c[i] = 0;
   }
   else
   {
    c[i] = 1;
   }
  }
 }
 a[15000] = 1;
 /*@ loop invariant 0 <= i <= 100000;
     loop assigns i; */
 for (i = 0; i < 100000; i++)
 {
  if (i == 15000 )
  {
   __VERIFIER_assert(c[i] == 0);
  }
 }
 return 0;
}
