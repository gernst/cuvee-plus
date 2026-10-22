// ./Cuvee.sh -quiet examples/boogie/parsing/loop_local.bpl
var g: int; var h: int; procedure set() modifies g; { g := 0; }
procedure p() { var x: int; while (true) modifies x; { } }
