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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "string-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }

extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}


/*@ assigns \nothing; */
extern char __VERIFIER_nondet_char();

int main()
{
  char string_A[5], string_B[5];
  int i, j, nc_A, nc_B, found=0;

  /*@ loop invariant 0 <= i <= 5;
      loop assigns i, string_A[0..4]; */
  for(i=0; i<5; i++)
    string_A[i]=__VERIFIER_nondet_char();
  if (!(string_A[5 -1]=='\0')) return 0;

  /*@ loop invariant 0 <= i <= 5;
      loop assigns i, string_B[0..4]; */
  for(i=0; i<5; i++)
    string_B[i]=__VERIFIER_nondet_char();
  if (!(string_B[5 -1]=='\0')) return 0;

  nc_A = 0;
  /*@ loop invariant 0 <= nc_A <= 4;
      loop invariant \forall integer t; 0 <= t < nc_A ==> string_A[t] != '\0';
      loop assigns nc_A; */
  while(string_A[nc_A]!='\0')
    nc_A++;

  nc_B = 0;
  /*@ loop invariant 0 <= nc_B <= 4;
      loop invariant \forall integer t; 0 <= t < nc_B ==> string_B[t] != '\0';
      loop assigns nc_B; */
  while(string_B[nc_B]!='\0')
    nc_B++;

  if (!(nc_B >= nc_A)) return 0;


  i=j=0;
  /*@ loop invariant 0 <= i <= nc_A;
      loop invariant 0 <= j <= nc_B;
      loop invariant j <= i;
      loop assigns i, j; */
  while((i<nc_A) && (j<nc_B))
  {
    if(string_A[i] == string_B[j])
    {
       i++;
       j++;
    }
    else
    {
       i = i-j+1;
       j = 0;
    }
  }

  found = (j>nc_B-1);

  __VERIFIER_assert(found == 0 || found == 1);

  return 0;
}
