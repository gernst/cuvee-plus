// ./Cuvee.sh -print null examples/dafny/parsing/datatypes/annotation.dfy
datatype list<a> = nil | cons(head: a, tail: list<a>) function f(xs: list<int>): bool { xs != nil as list<int> }
