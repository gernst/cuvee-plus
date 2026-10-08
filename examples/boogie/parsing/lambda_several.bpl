// ./Cuvee.sh -print null examples/boogie/parsing/lambda_several.bpl
// maps of several indices are curried
axiom (lambda x: int, y: int :: x)[0, 1] == 0;
