// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-invgen/NetBSD_loop.dfy
// SV-COMP loop-invgen/NetBSD_loop.yml (expected: safe), translated from the C program by hand: p
// counts from 0 to MAXPATHLEN, and stays within 0 and MAXPATHLEN
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var M: int;
  var p: int;
  M := *;
  if !(M > 0) {
    return;
  }
  p := 0;
  while p <= M {
    assert 0 <= p;
    assert p < M + 1;
    p := p + 1;
  }
}

// remaining goals of -teq -simplify:
// none
