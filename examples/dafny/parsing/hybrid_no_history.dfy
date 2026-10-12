// ./Cuvee.sh -vcgen -print null examples/dafny/parsing/hybrid_no_history.dfy
method p() { } method m() { parallel { p(); } }
