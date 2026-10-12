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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_two_index_09.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
int main( )
{
  int a[100000];
  int b[100000];
  int i = 0;
  int j = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop assigns i, b[0..99999]; */
  while( i < 100000 )
  {
	b[i] = __VERIFIER_nondet_int();
    i = i+1;
  }
  i = 1;
  /*@ loop invariant i == 9*j + 1;
      loop invariant 0 <= j;
      loop invariant \forall integer t; 0 <= t < j ==> a[t] == b[9*t+1];
      loop assigns i, j, a[0..99999]; */
  while( i < 100000 )
  {
 a[j] = b[i];
        i = i+9;
        j = j+1;
  }
  i = 1;
  j = 0;
  /*@ loop invariant i == 9*j + 1;
      loop invariant 0 <= j;
      loop invariant \forall integer t; 0 <= t && 9*t+1 < 100000 ==> a[t] == b[9*t+1];
      loop assigns i, j; */
  while( i < 100000 )
  {
 __VERIFIER_assert( a[j] == b[9*j+1] );
        i = i+9;
        j = j+1;
  }
  return 0;
}
