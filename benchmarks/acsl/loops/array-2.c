// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (array[0] may equal menor), the invariants are those of array-1
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array-2.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();

int main()
{
  unsigned int SIZE=1;
  unsigned int j,k;
  int array[SIZE], menor;
  
  menor = __VERIFIER_nondet_int();

  /*@ loop invariant 0 <= j <= SIZE;
      loop invariant \forall integer t; 0 <= t < j ==> menor <= array[t];
      loop assigns j, menor, array[0..SIZE-1]; */
  for(j=0;j<SIZE;j++) {
       array[j] = __VERIFIER_nondet_int();
       
       if(array[j]<=menor)
          menor = array[j];                          
    }                       
    
    __VERIFIER_assert(array[0]>menor);    

    return 0;
}

