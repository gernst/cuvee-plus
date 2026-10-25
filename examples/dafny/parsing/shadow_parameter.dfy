// ./Cuvee.sh -quiet examples/dafny/parsing/shadow_parameter.dfy
// parameters must not have the name of a global variable, which a call may modify (see Call)
var g: int; method m(g: int) { }
