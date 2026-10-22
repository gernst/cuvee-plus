// ./Cuvee.sh -quiet examples/boogie/parsing/call_loop_modifies.bpl
var g: int; var h: int; procedure set() modifies g; { g := 0; }
procedure p() modifies g; { while (true) modifies g; { call set(); } }
