// ./Cuvee.sh -quiet examples/dafny/parsing/functions_lambda_curried.dfy
function f(): int -> bool -> int { (x: int) => (b: bool) => x }
