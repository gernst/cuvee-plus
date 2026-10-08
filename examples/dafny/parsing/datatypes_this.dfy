// ./Cuvee.sh -print null examples/dafny/parsing/datatypes_this.dfy
// inside the members of a type, its fields, functions, and methods are accessible without this
datatype pair = pair(fst: int, snd: int) { function sum(): int { fst + snd } function twice(): int { sum() + this.sum() } }
