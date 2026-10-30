// ./Cuvee.sh -quiet examples/dafny/parsing/annotate_scope.dfy
// the variables of an annotation must be in scope at every statement with its tag, as in SV-LIB: k is not at the
// second loop

method main(n: int) returns (result: int) {
  {
    var k: int;
    k := 0;
    while {:tag "loop"} k < n {
      k := k + 1;
    }
  }
  result := n;
  while {:tag "loop"} 0 < result {
    result := result - 1;
  }
}
annotate "loop" {:invariant 0 <= k}
