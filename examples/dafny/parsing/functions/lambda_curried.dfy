// ./Cuvee.sh -print null examples/dafny/parsing/functions/lambda_curried.dfy
function f(): int -> bool -> int { (x: int) => (b: bool) => x }
