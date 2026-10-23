// ./Cuvee.sh -teq -prove benchmarks/monocera/polished_tests/cuvee/forall/simple_array_index_value_2.c
/* Benchmark used to verify Chimdyalwar, Bharti, et al. "VeriAbs: Verification by abstraction (competition contribution)." 
International Conference on Tools and Algorithms for the Construction and Analysis of Systems. Springer, Berlin, Heidelberg, 2017.*/

// #define SIZE 10000
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond)
{
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

unsigned int __VERIFIER_nondet_uint();

int main()
{
  unsigned int array[10000];
  unsigned int index;

  for (index = 0; index < 10000; index++) {
    unsigned int tmp = __VERIFIER_nondet_uint();
    assume_abort_if_not(tmp > index);
    array[index] = tmp;
  }

  for (index = 0; index < 10000; index++) {
    __VERIFIER_assert(array[index] > index);
  }

}
