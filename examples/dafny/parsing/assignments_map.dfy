// ./Cuvee.sh -quiet examples/dafny/parsing/assignments_map.dfy
method m(n: map<int, bool>) returns (o: map<int, bool>) { o := n; o[0] := true; }
