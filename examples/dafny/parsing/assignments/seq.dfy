// ./Cuvee.sh -print null examples/dafny/parsing/assignments/seq.dfy
method m(s: seq<int>) returns (t: seq<int>) { t := s; t[0] := 1; }
