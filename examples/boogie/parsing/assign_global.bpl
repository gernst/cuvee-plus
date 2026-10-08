// ./Cuvee.sh -print null examples/boogie/parsing/assign_global.bpl
// global variables may be assigned and modified by calls only if they are declared as modified
var g: int; var h: int; procedure set() modifies g; { g := 0; }
procedure p() modifies h; { g := 1; }
