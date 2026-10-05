// type aliases are unfolded during type checking
type pred<a> = array<a, bool>

function mem<a>(s: pred<a>, x: a): bool { s[x] }

// axioms and lemmas with type parameters
axiom <a> {:rw} forall s: pred<a>, x: a :: mem(s, x) == s[x]

datatype d = d(f: int)
{
  method id<b>(x: b) returns (y: b)
}

// calls are checked against the signature of the method
method m(s: d) returns (y: int)
{
  y := s.id(1);
}

// tuple types, whose components are numbered from 0
function swap(p: (int, bool)): (bool, int)
{
  (p.1, p.0)
}

// strings, which are String in SMT-LIB
function greeting(name: string): string
{
  if name == "" then "hello" else name
}
