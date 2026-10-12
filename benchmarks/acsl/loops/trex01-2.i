// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

/*@ requires \false;
    assigns \nothing; */
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "trex01-2.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
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
_Bool __VERIFIER_nondet_bool();
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
/*@ assigns \nothing; */
void f(int d) {
  int x = __VERIFIER_nondet_int(), y = __VERIFIER_nondet_int(), k = __VERIFIER_nondet_int(), z = 1;
  L1:
  if (!(k <= 1073741823))
    return;
  /*@ loop invariant z >= 1;
      loop assigns z; */
  while (z < k) { z = 2 * z; }
  __VERIFIER_assert(z>=1);
  L2:
  if (!(x <= 1000000 && x >= -1000000)) return;
  if (!(y <= 1000000 && y >= -1000000)) return;
  if (!(k <= 1000000 && k >= -1000000)) return;
  /*@ loop assigns x, y, z; */
  while (x > 0 && y > 0) {
    _Bool c = __VERIFIER_nondet_bool();
    if (c) {
      P1:
      x = x - d;
      y = __VERIFIER_nondet_bool();;
      z = z - 1;
    } else {
      y = y - d;
    }
  }
}
int main() {
  _Bool c = __VERIFIER_nondet_bool();
  if (c) {
    f(1);
  } else {
    f(2);
  }
  return 0;
}
