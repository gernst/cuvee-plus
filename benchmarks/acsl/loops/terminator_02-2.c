// ACSL annotations added by hand (benchmarks/acsl/README.md): the assertion is the negation of the loop condition
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "terminator_02-2.c", 3, "reach_error"); }

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
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
/*@ assigns \nothing; */
_Bool __VERIFIER_nondet_bool();

int main()
{
    int x=__VERIFIER_nondet_int();
    int z=__VERIFIER_nondet_int();
    if (!(x>-100)) return 0;
    if (!(x<200)) return 0;
    if (!(z>100)) return 0;
    if (!(z<200)) return 0;
    /*@ loop invariant x < 200;
        loop invariant z < 200;
        loop assigns x, z; */
    while(x<100 && z>100) 
    {
        _Bool tmp=__VERIFIER_nondet_bool();
        if (tmp) {
            x++;
        } else {
            x--;
            z--;
        }
    }                       

    __VERIFIER_assert(x>=100 || z<=100);

    return 0;
}


