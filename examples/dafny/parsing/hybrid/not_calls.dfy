// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid/not_calls.dfy
// parallel composition of other statements is parsed, but not verified
method m() returns (x: int, y: int) { parallel { x := 1; y := 2; } }
