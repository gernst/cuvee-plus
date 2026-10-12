// ACSL annotations added by hand (benchmarks/acsl/README.md); the ranges of the unsigned variables that the loops assign are loop invariants
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "nested5-1.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main()
{
  unsigned int x = 0;
  unsigned int y = 0;
  unsigned int z = 0;
  unsigned int w = 0;
  unsigned int v = 0;
  /*@ loop invariant w <= 0x0fffffff;
      loop invariant 0 <= x <= 4294967295;
      loop invariant 0 <= y <= 4294967295;
      loop invariant 0 <= z <= 4294967295;
      loop invariant 0 <= w <= 4294967295;
      loop invariant 0 <= v <= 4294967295;
      loop assigns w, x, y, z, v; */
  for(w=0;w<0x0fffffff;w++)
  	/*@ loop invariant x <= 10;
  	    loop invariant 0 <= x <= 4294967295;
  	    loop invariant 0 <= y <= 4294967295;
  	    loop invariant 0 <= z <= 4294967295;
  	    loop invariant 0 <= v <= 4294967295;
  	    loop assigns x, y, z, v; */
  	for(x=0;x< 10;x++)
	   /*@ loop invariant y <= 10;
	       loop invariant 0 <= y <= 4294967295;
	       loop invariant 0 <= z <= 4294967295;
	       loop invariant 0 <= v <= 4294967295;
	       loop assigns y, z, v; */
	   for(y=0;y< 10;y++)
		/*@ loop invariant z <= 10;
		    loop invariant 0 <= z <= 4294967295;
		    loop invariant 0 <= v <= 4294967295;
		    loop assigns z, v; */
		for(z=0;z< 10;z++) {
			/*@ loop invariant v <= 10;
			    loop invariant 0 <= v <= 4294967295;
			    loop assigns v; */
			for(v=0;v< 10;v++);
			__VERIFIER_assert(v % 4);
	   }
  return 0;
}
