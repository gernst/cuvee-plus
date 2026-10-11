// ./Cuvee.sh -verify -z3 examples/c/parsing/overflow.c
// unsigned integers wrap around, after arithmetic and when converted from other types, e.g. -1, and comparisons are
// in the common type of their operands, e.g. -1 < 1u is false
int main(void) {
  unsigned int x = 0;
  x = x - 1;
  assert(x == 4294967295);
  x++;
  assert(x == 0);
  unsigned char c = 255;
  c += 1;
  assert(c == 0);
  int i = -1;
  assert(!(i < 1u));
  unsigned short s = -1;
  assert(s == 65535);
  unsigned long long l = (unsigned long long) i;
  assert(l == 18446744073709551615ull);
  unsigned int y = __VERIFIER_nondet_uint();
  unsigned int z = y + 1;
  assert(z > y || z == 0);
  return 0;
}
