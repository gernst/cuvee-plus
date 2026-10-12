// ./Cuvee.sh -vcgen -print null examples/c/parsing/invalid_acsl_assigns.c
// without -teq and -chc, the loop assigns clause is the modifies clause of the loop, which must list the global
// variable g that the body assigns; the local variable i is inferred
int g;

int main(void) {
  /*@ loop invariant 0 <= i <= 10;
      loop assigns i; */
  for (int i = 0; i < 10; i++) {
    g = i;
  }
  return 0;
}
