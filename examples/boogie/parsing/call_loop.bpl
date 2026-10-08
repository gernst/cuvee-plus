// ./Cuvee.sh -print null examples/boogie/parsing/call_loop.bpl
var g: int; var h: int; procedure set() modifies g; { g := 0; }
procedure p() modifies g; { while (true) { call set(); } }
