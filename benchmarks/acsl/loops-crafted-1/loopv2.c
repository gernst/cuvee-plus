// ACSL annotations added by hand (benchmarks/acsl/README.md): the second loop never terminates (j stays even)
int SIZE = 50000001;
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "loopv2.c", 5, "reach_error"); }
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
int __VERIFIER_nondet_int();
int main() {
  int n,i,j,k;
  n = __VERIFIER_nondet_int();
  if (!(n <= SIZE)) return 0;
  i = 0; j=0;
  /*@ loop invariant i % 4 == 0;
      loop invariant (i == 0 && j == 0) || j == i + 2;
      loop assigns i, j; */
  while(i<n){ 

    i = i + 4;
    j = i +2;    
  }
  k =i;
  /*@ loop invariant j % 2 == 0;
      loop invariant k % 2 == 0;
      loop assigns j, k; */
  while( (j%2) == 0){
   j-=4;
   k -=4; 
  }
  __VERIFIER_assert( (k%2) == 0 );
  return 0;
}
