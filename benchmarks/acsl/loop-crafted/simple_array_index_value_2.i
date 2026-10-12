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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "simple_array_index_value_2.c", 7, __extension__ __PRETTY_FUNCTION__); })); }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond)
{
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

/*@ assigns \nothing; */
unsigned int __VERIFIER_nondet_uint();

int main()
{
  unsigned int array[10000];
  unsigned int index;

  /*@ loop invariant 0 <= index <= 10000;
      loop invariant \forall integer t; 0 <= t < index ==> array[t] > t;
      loop assigns index, array[0..9999]; */
  for (index = 0; index < 10000; index++) {
    unsigned int tmp = __VERIFIER_nondet_uint();
    assume_abort_if_not(tmp > index);
    array[index] = tmp;
  }

  /*@ loop invariant 0 <= index <= 10000;
      loop invariant \forall integer t; 0 <= t < 10000 ==> array[t] > t;
      loop assigns index; */
  for (index = 0; index < 10000; index++) {
    __VERIFIER_assert(array[index] > index);
  }

}
