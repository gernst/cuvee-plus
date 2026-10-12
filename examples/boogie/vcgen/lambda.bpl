// ./Cuvee.sh -vcgen -monomorph -z3 examples/boogie/vcgen/lambda.bpl
// expected: valid
// lambdas, which are maps, applied like maps, also as the value of a function,
// and maps of several indices, which are nested maps, also lambdas of several variables

const n: int;

function shift(): [int]int { (lambda x: int :: x + n) }

procedure p(k: int) returns (a: [int]int)
  ensures a[k] == k + n;
  ensures a == shift();
{
  a := (lambda x: int :: x + n);
}

procedure q(i: int, j: int) returns (m: [int, int]int)
  ensures i != j ==> m[i, j] == i + j;
  ensures m[i, i] == 0;
{
  m := (lambda x: int, y: int :: x + y);
  m[i, i] := 0;
}
