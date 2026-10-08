// ./Cuvee.sh -print null examples/dafny/parsing/datatypes_tester_call.dfy
datatype list<a> = nil | cons(head: a, tail: list<a>) function g(): list<int> function f(): bool { g().nil? }
