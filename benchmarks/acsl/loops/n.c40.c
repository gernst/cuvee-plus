// ACSL annotations added by hand (benchmarks/acsl/README.md): the global x is zero, so the loop never runs
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "n.c40.c", 3, "reach_error"); }

/*@ assigns \nothing; */
int __VERIFIER_nondet_int();

  char x[100], y[100];
  int i,j,k;

int main() {  
  k = __VERIFIER_nondet_int();
  
  i = 0;
  /*@ loop invariant i == 0;
      loop invariant \forall integer t; 0 <= t < 100 ==> x[t] == 0;
      loop assigns i, y[0..99]; */
  while(x[i] != 0){
    y[i] = x[i];
    i++;
  }
  y[i] = 0;
  
  if(k >= 0 && k < i)
    if(y[k] == 0)
      {ERROR: {reach_error();abort();}}

  return 0;
}
