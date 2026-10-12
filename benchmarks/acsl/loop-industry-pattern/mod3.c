// ACSL annotations added by hand (benchmarks/acsl/README.md); the ranges of the unsigned variables that the loops assign are loop invariants
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "mod3.c", 3, "reach_error"); }

// Category: Loops
// Verification result: TRUE
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond){
  if(!(cond))
  ERROR: {reach_error();abort();}
  return;
}

int main(){
  unsigned int x = __VERIFIER_nondet_int();
  unsigned int y = 1;
  
  /*@ loop invariant y == 0 || y == 1;
      loop invariant y == 0 ==> x % 3 == 0;
      loop invariant 0 <= x <= 4294967295;
      loop invariant 0 <= y <= 4294967295;
      loop assigns x, y; */
  while(__VERIFIER_nondet_int()){
    if(x % 3 == 1){
      x += 2; y = 0;}
    else{
      if(x % 3 == 2){
	x += 1; y = 0;}
      else{
	if(__VERIFIER_nondet_int()){
	  x += 4; y = 1;}
	else{
	  x += 5; y = 1;}
      }
    }
  }
  if(y == 0)
    __VERIFIER_assert(x % 3 == 0);
  return 0;
}

  
