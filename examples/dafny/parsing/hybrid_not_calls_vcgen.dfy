// ./Cuvee.sh -hybrid -vcgen -quiet examples/dafny/parsing/hybrid_not_calls_vcgen.dfy
method m() returns (x: int, y: int) { parallel { x := 1; y := 2; } }
