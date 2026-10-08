// ./Cuvee.sh -teq -print null examples/dafny/parsing/teq_no_body.dfy
// a procedure without a body cannot be inlined
method f(x: int) returns (y: int)
method g() returns (z: int) { z := f(1); }
