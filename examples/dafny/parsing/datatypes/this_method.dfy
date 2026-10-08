// ./Cuvee.sh -print null examples/dafny/parsing/datatypes/this_method.dfy
datatype pair = pair(fst: int, snd: int) { method get() returns (x: int) { x := fst; } method get2() returns (y: int) { y := get(); } }
