// ./Cuvee.sh examples/boogie/printing/tags.bpl
// the tags of SV-LIB and the commands annotate-tag and verify-call in the dialect of Boogie (see
// examples/svlib/printing/tagged_sequence_bpl.svlib), which read back as the SV-LIB script

procedure {:tag "main"} main(l: int, n: int) returns (result: int) {
  var i: int;
  i := l;
  if (!(0 < l)) {
    result := 0;
    return;
  }
  while {:tag "main-while-1"} (i < n) {
    i := i + 1;
  }
  {:tag "main-check-1"} {:check-true 0 < i} {}
  result := 0;
  return;
}

annotate "main-check-1" {:check-true 1 <= l};

annotate "main-while-1" {:invariant l <= i};

verify main(1, 5);
