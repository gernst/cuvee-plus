// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "eureka_01-2.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int INFINITY = 899;

int main(){
  int nodecount = 5;
  int edgecount = 20;
  int source = 0;
  int Source[20] = {0,4,1,1,0,0,1,3,4,4,2,2,3,0,0,3,1,2,2,3};
  int Dest[20] = {1,3,4,1,1,4,3,4,3,0,0,0,0,2,3,0,2,1,0,4};
  int Weight[20] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19};
  int distance[5];
  int x,y;
  int i,j;
  
  /*@ loop invariant 0 <= i <= nodecount;
      loop invariant \forall integer t; 0 <= t < i ==> 0 <= distance[t] <= INFINITY;
      loop assigns i, distance[0..4]; */
  for(i = 0; i < nodecount; i++){
    if(i == source){
      distance[i] = 0;
    }
    else {
      distance[i] = INFINITY;
    }
  }

  /*@ loop invariant 0 <= i <= nodecount;
      loop invariant \forall integer t; 0 <= t < nodecount ==> 0 <= distance[t] <= INFINITY;
      loop invariant \forall integer t; 0 <= t < edgecount ==> 0 <= Dest[t] < nodecount && 0 <= Source[t] < nodecount && Weight[t] >= 0;
      loop assigns i, j, x, y, distance[0..4]; */
  for(i = 0; i < nodecount; i++)
    {
      /*@ loop invariant 0 <= j <= edgecount;
          loop invariant \forall integer t; 0 <= t < nodecount ==> 0 <= distance[t] <= INFINITY;
          loop invariant \forall integer t; 0 <= t < edgecount ==> 0 <= Dest[t] < nodecount && 0 <= Source[t] < nodecount && Weight[t] >= 0;
          loop assigns j, x, y, distance[0..4]; */
      for(j = 0; j < edgecount; j++)
	{
	  x = Dest[j];
	  y = Source[j];
	  if(distance[x] > distance[y] + Weight[j])
	    {
	      distance[x] = distance[y] + Weight[j];
	    }
	}
    }
  /*@ loop invariant 0 <= i <= edgecount;
      loop invariant \forall integer t; 0 <= t < nodecount ==> 0 <= distance[t] <= INFINITY;
      loop invariant \forall integer t; 0 <= t < edgecount ==> 0 <= Dest[t] < nodecount && 0 <= Source[t] < nodecount && Weight[t] >= 0;
      loop assigns i, x, y; */
  for(i = 0; i < edgecount; i++)
    {
      x = Dest[i];
      y = Source[i];
      if(distance[x] > distance[y] + Weight[i])
	{
	  return 0;
	}
    }

  /*@ loop invariant 0 <= i <= nodecount;
      loop invariant \forall integer t; 0 <= t < nodecount ==> 0 <= distance[t] <= INFINITY;
      loop assigns i; */
  for(i = 0; i < nodecount; i++)
    {
      __VERIFIER_assert(distance[i]>=0);
    }

  return 0;
}

