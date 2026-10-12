// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (str2 is filled with str1[0]), the loop invariants bound the indices
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "invert_string-1.c", 3, "reach_error"); }
extern void abort(void);

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
char __VERIFIER_nondet_char();
/*@ assigns \nothing; */
unsigned int __VERIFIER_nondet_uint();

int main() {
    int MAX = __VERIFIER_nondet_uint();
    if(!(MAX > 0)) {abort();}
    char str1[MAX], str2[MAX];
    int cont, i, j;
    cont = 0;
    
    /*@ loop invariant 0 <= i <= MAX;
        loop assigns i, str1[0..MAX-1]; */
    for (i=0; i<MAX; i++) {
        str1[i]=__VERIFIER_nondet_char();
    }
	str1[MAX-1]= '\0';

    j = 0;
    
    /*@ loop invariant -1 <= i <= MAX-1;
        loop invariant j == MAX-1-i;
        loop assigns i, j, str2[0..MAX-1]; */
    for (i = MAX - 1; i >= 0; i--) {
        str2[j] = str1[0];
        j++;
    }

    j = MAX-1;
    /*@ loop invariant 0 <= i <= MAX;
        loop invariant j == MAX-1-i;
        loop assigns i, j; */
    for (i=0; i<MAX; i++) {
      __VERIFIER_assert(str1[i] == str2[j]);
	  j--;
    }
}
