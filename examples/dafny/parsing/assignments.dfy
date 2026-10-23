// ./Cuvee.sh examples/dafny/parsing/assignments.dfy
// assignments to elements are updates of maps and sequences
method update_map(n: map<int, bool>) returns (o: map<int, bool>) { o := n; o[0] := true; }
method update_seq(s: seq<int>) returns (t: seq<int>) { t := s; t[0] := 1; }
