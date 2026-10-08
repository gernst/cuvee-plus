// ./Cuvee.sh examples/dafny/printing/mixfix.dfy
// operators by precedence and associativity, one expression per function, such that comparisons do not chain
function f1(x: int, y: int, p: bool, q: bool): bool { x + y + 0 == x + (y + 0) }
function f2(x: int, y: int, p: bool, q: bool): bool { (x + y) * (x - y) == 0 }
function f3(x: int, y: int, p: bool, q: bool): bool { p ==> q ==> p }
function f4(x: int, y: int, p: bool, q: bool): bool { (p ==> q) ==> p }
function f5(x: int, y: int, p: bool, q: bool): bool { (p || q) && x < y }
function f6(x: int, y: int, p: bool, q: bool): bool { (x < y) == p }
function f7(x: int, y: int, p: bool, q: bool): bool { p == (q == p) }
