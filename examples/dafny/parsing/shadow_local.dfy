// ./Cuvee.sh -quiet examples/dafny/parsing/shadow_local.dfy
// local variables must not have the name of a global variable, which a call may modify (see Call)
var g: int; method m() { var g: int; g := 1; }
