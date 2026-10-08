// ./Cuvee.sh -print null examples/dafny/parsing/assignments/map.dfy
method m(n: map<int, bool>) returns (o: map<int, bool>) { o := n; o[0] := true; }
