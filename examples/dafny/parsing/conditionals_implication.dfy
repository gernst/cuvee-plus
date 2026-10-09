// ./Cuvee.sh -print smt2 examples/dafny/parsing/conditionals_implication.dfy
// if without else is an implication, also below quantifiers and inside of expressions,
// and else belongs to the innermost if, which must have one
predicate p(x: int)
predicate q(x: int)
axiom if p(0) then q(0) && q(1)
lemma q_1(x: int)
  requires p(x)
  ensures q(x)
{}
goal if p(0) then if q(0) then p(1) else q(1)
axiom if p(0) then q(0) else q(1)
axiom (if p(0) then q(0)) == q(1)
