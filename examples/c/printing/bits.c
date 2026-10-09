// ./Cuvee.sh examples/c/printing/bits.c
// shifts by constants are multiplications and divisions by powers of 2, the other shifts and the bit operations on
// integers are declared functions of the prelude, which are printed as the operators again
int main(void) {
  int x = 12, y = 5, z;
  z = x << 2;
  z = x >> 1;
  z = x << y;
  z = (x & y) | (x ^ ~y);
  z &= 3;
  z |= 4;
  z ^= x;
  z <<= 1;
  z >>= y;
  return z;
}
