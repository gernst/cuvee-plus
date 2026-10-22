// ./Cuvee.sh -quiet examples/dafny/parsing/assignments_seq.dfy
method m(s: seq<int>) returns (t: seq<int>) { t := s; t[0] := 1; }
