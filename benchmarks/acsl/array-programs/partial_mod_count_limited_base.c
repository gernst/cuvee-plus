// ACSL annotations added by hand (benchmarks/acsl/README.md): the zeros of a are the multiples of R above the threshold, counted in closed form with integer division
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "partial_mod_count_limited_base.c", 3, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
int N = 1000000;
int main(){
int i,j=0,k=0,a[N];
  unsigned int R=__VERIFIER_nondet_int();
 assume_abort_if_not(R>0);
  /*@ loop invariant 0 <= i <= N;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == ((t > N/2 && t % R == 0 && (t-1)/R - (N/2)/R < 1) ? 0 : t+1);
      loop invariant k == \min(1, (i >= N/2 + 2 ? (i-1)/R - (N/2)/R : 0));
      loop assigns i, k, a[0..N-1]; */
  for(i=0;i<N;i++){
    a[i]=i+1;
    if(i>N/2 && k<1)
       a[i]=i%R;
    if(a[i]==0) k++;
  }
  /*@ loop invariant 0 <= i <= N;
      loop invariant \forall integer t; 0 <= t < N ==> a[t] == ((t > N/2 && t % R == 0 && (t-1)/R - (N/2)/R < 1) ? 0 : t+1);
      loop invariant j == \min(1, (i >= N/2 + 2 ? (i-1)/R - (N/2)/R : 0));
      loop assigns i, j; */
  for(i=0;i<N;i++){
    if (a[i]==0) j++;
     __VERIFIER_assert(j < 2);
  }
  return 0;
}

