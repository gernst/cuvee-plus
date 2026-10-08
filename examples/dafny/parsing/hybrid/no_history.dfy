// ./Cuvee.sh -verify -print null examples/dafny/parsing/hybrid/no_history.dfy
method p() { } method m() { parallel { p(); } }
