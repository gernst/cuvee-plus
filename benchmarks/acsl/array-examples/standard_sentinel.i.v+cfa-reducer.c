// ACSL annotations added by hand (benchmarks/acsl/README.md): an output of a reducer (an unrolled control flow with gotos), only the harness is annotated
int __return_main;
/*@ assigns \nothing;
    ensures \false; */
void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "standard_sentinel.i.v+cfa-reducer.c", 4, "reach_error"); }
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond);
int main();
int __return_60;
 int main()
 {
 int main__a[100000];
 int main__marker;
 main__marker = __VERIFIER_nondet_int();
 int main__pos;
 main__pos = __VERIFIER_nondet_int();

	for(int i = 0; i < 100000; i++) 
	{
	  main__a[i] = __VERIFIER_nondet_int();
	}
	
 if (main__pos >= 0)
 {
 if (main__pos < 100000)
 {
 main__a[main__pos] = main__marker;
 int main__i = 0;
 label_47:; 
 if ((main__a[main__i]) != main__marker)
 {
 main__i = main__i + 1;
 goto label_47;
 }
 else 
 {
 {
 int __tmp_1;
 __tmp_1 = main__i <= main__pos;
 int __VERIFIER_assert__cond;
 __VERIFIER_assert__cond = __tmp_1;
 if (__VERIFIER_assert__cond == 0)
 {
 {reach_error();}
 return __return_main;
 }
 else 
 {
  __return_60 = 0;
 return __return_60;
 }
 }
 }
 }
 else 
 {
 return __return_main;
 }
 }
 else 
 {
 return __return_main;
 }
 }
