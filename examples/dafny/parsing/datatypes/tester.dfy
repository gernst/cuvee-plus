// ./Cuvee.sh -print null examples/dafny/parsing/datatypes/tester.dfy
datatype list<a> = nil | cons(head: a, tail: list<a>) function f(xs: list<int>): bool { xs.cons? && !xs.nil? }
