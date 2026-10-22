// ./Cuvee.sh -quiet examples/c/parsing/invalid_acsl_loop.c
// loop annotations precede a loop
int main(void) {
  int x = 0;
  //@ loop invariant x >= 0;
  x = 1;
  return x;
}
