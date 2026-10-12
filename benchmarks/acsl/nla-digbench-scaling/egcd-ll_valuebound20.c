// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/egcd-ll
/* extended Euclid's algorithm */
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "egcd-ll.c", 4, "reach_error"); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
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
    ERROR:
        {reach_error();}
    }
    return;
}

int main() {
    long long a, b, p, q, r, s;
    int x, y;
    x = __VERIFIER_nondet_int();
    assume_abort_if_not(x>=0 && x<=20);
    y = __VERIFIER_nondet_int();
    assume_abort_if_not(y>=0 && y<=20);
    assume_abort_if_not(x >= 1);
    assume_abort_if_not(y >= 1);

    a = x;
    b = y;
    p = 1;
    q = 0;
    r = 0;
    s = 1;

    /*@ loop invariant p*s - r*q == 1;
        loop invariant a == y*r + x*p;
        loop invariant b == x*q + y*s;
        loop invariant a >= 1 && b >= 1;
        loop assigns a, b, p, q, r, s; */
    while (1) {
        __VERIFIER_assert(1 == p * s - r * q);
        __VERIFIER_assert(a == y * r + x * p);
        __VERIFIER_assert(b == x * q + y * s);

        if (!(a != b))
            break;

        if (a > b) {
            a = a - b;
            p = p - q;
            r = r - s;
        } else {
            b = b - a;
            q = q - p;
            s = s - r;
        }
    }
    
    __VERIFIER_assert(a - b == 0);    
    __VERIFIER_assert(p*x + r*y - b == 0);
    __VERIFIER_assert(q*r - p*s + 1 == 0);
    __VERIFIER_assert(q*x + s*y - b == 0);
    return 0;
}
