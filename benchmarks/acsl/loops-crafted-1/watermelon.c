// ACSL annotations added by hand (benchmarks/acsl/README.md): the contracts assume the globals true == 1 and false == 0, which ACSL cannot name
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "watermelon.c", 3, "reach_error"); }
/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint(void);
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
      ERROR: {reach_error();abort();}
  }
  return;
}

int true = 1;
int false = 0;

/*@ assigns \nothing;
    ensures \result == ((w >= 4 && w % 2 == 0) ? 1 : 0); */
int correct_version(int w)
{
  int is_divisible = true;

  if(w < 4)
    is_divisible = false;
  else
  {
    int i;
    /*@ loop invariant 0 <= i <= w + 1;
        loop invariant i % 2 == 0;
        loop assigns i; */
    for(i = 0; i < w; i += 2)
    {}

    if(i != w)
      is_divisible = false;
  }

  return is_divisible;
}

/*@ assigns \nothing;
    ensures \result == ((w >= 4 && w % 2 == 0) ? 1 : 0); */
int student_version(int w)
{
  int is_divisible = true;

  if(w < 4)
    is_divisible = false;
  else
  {
    int i;
    /*@ loop invariant 0 <= i <= w + 1;
        loop invariant i % 2 == 0;
        loop assigns i; */
    for(i = 0; i < w; i += 2)
    {}

    if(i != w)
      is_divisible = false;
  }

  return is_divisible;
}

int main(){

  unsigned int w=__VERIFIER_nondet_uint();

  int is_divisible1 = true, is_divisible2 = true;

  if(w > 0 && w < 10000000)
  {
    is_divisible1 = correct_version(w);
    is_divisible2 = student_version(w);
    __VERIFIER_assert(is_divisible1 == is_divisible2);
  }
  return 0;

}

