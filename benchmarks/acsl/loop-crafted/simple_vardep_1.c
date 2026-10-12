// ACSL annotations added by hand (benchmarks/acsl/README.md)
/* Benchmark used to verify Chimdyalwar, Bharti, et al. "VeriAbs: Verification by abstraction (competition contribution)." 
International Conference on Tools and Algorithms for the Construction and Analysis of Systems. Springer, Berlin, Heidelberg, 2017.*/

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "simple_vardep_1.c", 6, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond)
{
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main()
{
  unsigned int i = 0;
  unsigned int j = 0;
  unsigned int k = 0;

  /*@ loop invariant j == 2*i;
      loop invariant k == 3*i;
      loop assigns i, j, k; */
  while (k < 0x0fffffff) {
    i = i + 1;
    j = j + 2;
    k = k + 3;

    __VERIFIER_assert(k == (i + j));
  }

}
