// ./Cuvee.sh -quiet examples/boogie/parsing/loop_global.bpl
var g: int; var h: int; procedure set() modifies g; { g := 0; }
procedure p() { while (true) modifies g; { } }
