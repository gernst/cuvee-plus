// ./Cuvee.sh -simplify examples/simplify/rules_printing.dfy
// the rules are printed with their attribute, which parses back
function f(x: int): int axiom {:rw} forall x: int :: f(f(x)) == x
