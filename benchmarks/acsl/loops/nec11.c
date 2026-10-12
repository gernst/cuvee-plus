// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (len <= 4 always)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "nec11.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

/*@ assigns \nothing; */
_Bool __VERIFIER_nondet_bool();

int main(){
   int a[5];
   int len=0;
   _Bool c=__VERIFIER_nondet_bool();
   int i;


   /*@ loop invariant 0 <= len <= 4;
       loop assigns len, a[0..4]; */
   while(c){
     
      if (len==4)
         len =0;
      
      a[len]=0;

      len++;
   }
   __VERIFIER_assert(len==5);
   return 1;

   
}
