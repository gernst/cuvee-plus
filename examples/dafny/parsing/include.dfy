// ./Cuvee.sh examples/dafny/parsing/include.dfy
// include "path" parses the file at path, relative to the including file, by a fresh parser that starts from the
// state after the prelude; its commands are part of the input and its declarations are known to the rest of it;
// an included file includes further files relative to its own directory (included/twice.dfy includes base.dfy)
include "included/twice.dfy"

lemma quadruple(x: int)
  ensures twice(twice(x)) == 4 * base(x) - 1
