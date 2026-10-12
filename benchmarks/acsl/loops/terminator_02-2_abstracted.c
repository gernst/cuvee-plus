// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
/*@ assigns \nothing; */
extern _Bool __VERIFIER_nondet_bool();
/*@ assigns \nothing; */
extern char __VERIFIER_nondet_char();
/*@ assigns \nothing; */
extern double __VERIFIER_nondet_double();
/*@ assigns \nothing; */
extern float __VERIFIER_nondet_float();
/*@ assigns \nothing; */
extern unsigned long __VERIFIER_nondet_ulong();
/*@ assigns \nothing; */
extern unsigned long long __VERIFIER_nondet_ulonglong();
/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "terminator_02-2_abstracted.c", 3, "reach_error"); }

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
_Bool __VERIFIER_nondet_bool();

int main()
{
    int x=__VERIFIER_nondet_int();
    int z=__VERIFIER_nondet_int();
    if (!(x>-100)) return 0;
    if (!(x<200)) return 0;
    if (!(z>100)) return 0;
    if (!(z<200)) return 0;
    // START HAVOCABSTRACTION
    if ((z > (100)) & (x < (100))) {
    z = __VERIFIER_nondet_int();
    x = __VERIFIER_nondet_int();
    }
    if ((z > (100)) & (x < (100))) abort();
    // END HAVOCABSTRACTION                       

    __VERIFIER_assert(x>=100 || z<=100);

    return 0;
}


