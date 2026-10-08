// ./Cuvee.sh -hybrid -verify -print null examples/dafny/parsing/hybrid_not_calls_verify.dfy
method m() returns (x: int, y: int) { parallel { x := 1; y := 2; } }
