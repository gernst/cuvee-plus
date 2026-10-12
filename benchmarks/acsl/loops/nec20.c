// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (j may exceed 1024)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "nec20.c", 3, "reach_error"); }
/*@ assigns \nothing; */
unsigned int __VERIFIER_nondet_uint();

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int b;
/*@ assigns \nothing; */
_Bool __VERIFIER_nondet_bool();
int main(){
   _Bool k=__VERIFIER_nondet_bool();
   unsigned int i,n,j;
   int a[1025];
   
   if (k){
      n=0;
   } else {
      n=1023;
   }

   i=0;
   j=__VERIFIER_nondet_uint();
   if (j > 10000)
     return 0;

   /*@ loop invariant 0 <= i <= n+1;
       loop invariant j == \at(j, LoopEntry) + 2*i;
       loop assigns i, j; */
   while ( i <= n){
      i++;
      j= j +2;
   }

   a[i]=0;
   __VERIFIER_assert(j<1025);
   a[j]=0;
   a[b]=0;
   if (b >= 0 && b < 1023)
      a[b]=1;
   else
      a[b%1023] =1;
   
   return 1;
  
}
