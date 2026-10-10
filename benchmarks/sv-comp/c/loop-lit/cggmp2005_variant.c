// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/cggmp2005_variant.c
// SV-COMP loop-lit/cggmp2005_variant.yml, translated from benchmarks/sv-comp/dafny/loop-lit/cggmp2005_variant.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int lo;
  int mid;
  int hi;
  lo = 0;
  mid = __VERIFIER_nondet_int();
  if (!(mid > 0)) {
    result = 0;
    return result;
  }
  hi = 2 * mid;
  while (mid > 0) {
    lo = lo + 1;
    hi = hi - 1;
    mid = mid - 1;
  }
  assert(lo == hi);
  result = 0;
  return result;
}

