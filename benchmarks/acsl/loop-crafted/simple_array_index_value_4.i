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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "simple_array_index_value_4.c", 7, __extension__ __PRETTY_FUNCTION__); })); }
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
  unsigned int array[100000];
  unsigned int index1;
  unsigned int index2;
  unsigned int loop_entered = 0;

  /*@ loop invariant 0 <= i <= 100000;
      loop assigns i, array[0..99999]; */
  for (unsigned i = 0; i < 100000; ++i) {
    array[i] = __VERIFIER_nondet_uint();
  }

  index1 = __VERIFIER_nondet_uint();
  assume_abort_if_not(index1 < 100000);
  index2 = __VERIFIER_nondet_uint();
  assume_abort_if_not(index2 < 100000);

  /*@ loop invariant index1 <= index2 + 1;
      loop invariant index1 < 100000;
      loop invariant index2 < 100000;
      loop invariant \forall integer t; \at(index1,LoopEntry) <= t < index1 ==> array[t] == array[index1 + index2 - t];
      loop assigns index1, index2, loop_entered; */
  while (index1 < index2) {
    __VERIFIER_assert((index1 < 100000) && (index2 < 100000));
    assume_abort_if_not(array[index1] == array[index2]);
    index1++;
    index2--;
    loop_entered = 1;
  }

  if (loop_entered) {
    /*@ loop invariant index2 <= index1 + 1;
        loop invariant index1 < 100000;
        loop invariant index2 < 100000;
        loop invariant \forall integer t; index2 <= t <= index1 ==> array[t] == array[index1 + index2 - t];
        loop assigns index1, index2; */
    while (index2 < index1) {
      __VERIFIER_assert(array[index1] == array[index2]);
      index2++;
      index1--;
    }
  }

}
