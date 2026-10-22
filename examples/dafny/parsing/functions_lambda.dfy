// ./Cuvee.sh -quiet examples/dafny/parsing/functions_lambda.dfy
function f(): (int, bool) -> int { (x: int, b: bool) => if b then x else 0 }
