// ACSL annotations added by hand (benchmarks/acsl/README.md)
typedef unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "array_ptr_partial_init.c", 5, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int *a[100000];
int i;
int main ()
{
 /*@ loop invariant 0 <= i <= 100000;
     loop assigns i, a[0..99999]; */
 for(i = 0; i < 100000; i++)
 {
  a[i] = 0;
 }
 /*@ loop invariant 0 <= i <= 50000;
     loop assigns i, a[0..49999]; */
 for(i = 0; i < 100000 / 2; i++)
 {
  a[i] = malloc(sizeof(int)) ;
 }
 /*@ loop invariant 0 <= i <= 50000;
     loop assigns i; */
 for(i = 0; i < 100000 / 2; i++)
 {
  __VERIFIER_assert(a[i] != 0);
 }
return 0;
}
