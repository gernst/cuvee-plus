// ./Cuvee.sh -teq -simplify -split -simplify examples/c/teq/unsigned_up.c
// an unsigned counter that wraps around modulo 2^32 (mods), whose test bounds it below 2^32, such that its final value
// is the bound itself, which is even
int main(void) { unsigned int x = 0;
  while (x < 268435454) { x = x + 2; }
  assert(x == 268435454); assert(x % 2 == 0); return 0; }
