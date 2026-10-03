// operators of different precedence and associativity, and if-then-else expressions
function abs(x: int): int { if x < 0 then -x else x }

function f(x: int, y: int): int { (x + y) * (x - y) - -1 + abs(x) * 2 }

predicate p(a: bool, b: bool, x: int) { (a ==> b ==> a) && (a || !b) && (x < 0) == a && !(a && b) }

predicate q(x: int) { (if x < 0 then 0 else x) + 1 > 0 }
