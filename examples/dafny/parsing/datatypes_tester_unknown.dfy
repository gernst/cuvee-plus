// ./Cuvee.sh -print null examples/dafny/parsing/datatypes_tester_unknown.dfy
datatype list<a> = nil | cons(head: a, tail: list<a>) function f(xs: list<int>): bool { xs.none? }
