// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (the elements are 47)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_init6_ground-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int main ( ) {
  int a [100000];
  int i = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == 42;
      loop assigns i, a[0..99999]; */
  while ( i < 100000 ) {
    a[i] = 42;
    i = i + 1;
  }
  i = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == 43;
      loop invariant \forall integer t; i <= t < 100000 ==> a[t] == 42;
      loop assigns i, a[0..99999]; */
  while ( i < 100000 ) {
    a[i] = 43;
    i = i + 1;
  }
  i = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == 44;
      loop invariant \forall integer t; i <= t < 100000 ==> a[t] == 43;
      loop assigns i, a[0..99999]; */
  while ( i < 100000 ) {
    a[i] = 44;
    i = i + 1;
  }
  i = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == 45;
      loop invariant \forall integer t; i <= t < 100000 ==> a[t] == 44;
      loop assigns i, a[0..99999]; */
  while ( i < 100000 ) {
    a[i] = 45;
    i = i + 1;
  }
  i = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == 46;
      loop invariant \forall integer t; i <= t < 100000 ==> a[t] == 45;
      loop assigns i, a[0..99999]; */
  while ( i < 100000 ) {
    a[i] = 46;
    i = i + 1;
  }
  i = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == 47;
      loop invariant \forall integer t; i <= t < 100000 ==> a[t] == 46;
      loop assigns i, a[0..99999]; */
  while ( i < 100000 ) {
    a[i] = 47;
    i = i + 1;
  }
  int x;
  /*@ loop invariant 0 <= x <= 100000;
      loop invariant \forall integer t; 0 <= t < 100000 ==> a[t] == 47;
      loop assigns x; */
  for ( x = 0 ; x < 100000 ; x++ ) {
    __VERIFIER_assert( a[x] == 46 );
  }
  return 0;
}
