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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_copy2_ground-2.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
int main( ) {
  int a1[100000];
  int a2[100000];
  int a3[100000];
  int a;
  /*@ loop invariant 0 <= a <= 100000;
      loop assigns a, a1[0..99999]; */
  for ( a = 0 ; a < 100000 ; a++ ) {
      a1[a] = __VERIFIER_nondet_int();
  }
  int i;
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < i ==> a2[t] == a1[t];
      loop assigns i, a2[0..99999]; */
  for ( i = 0 ; i < 100000 ; i++ ) {
    a2[i] = a1[i];
  }
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < 100000 ==> a2[t] == a1[t];
      loop invariant \forall integer t; 0 <= t < i ==> a3[t] == a2[t];
      loop assigns i, a3[0..99999]; */
  for ( i = 0 ; i < 100000 ; i++ ) {
    a3[i] = a2[i];
  }
  int x;
  /*@ loop invariant 0 <= x <= 100000;
      loop invariant \forall integer t; 0 <= t < 100000 ==> a2[t] == a1[t];
      loop invariant \forall integer t; 0 <= t < 100000 ==> a3[t] == a1[t];
      loop assigns x; */
  for ( x = 0 ; x < 100000 ; x++ ) {
    __VERIFIER_assert( a1[x] == a3[x] );
  }
  return 0;
}
