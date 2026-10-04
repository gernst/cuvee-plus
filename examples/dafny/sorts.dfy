// type aliases are unfolded during type checking
type pred<a> = array<a, bool>

function mem<a>(s: pred<a>, x: a): bool { s[x] }

datatype d = d(f: int)
{
  method id<b>(x: b) returns (y: b)
}

// calls are checked against the signature of the method
method m(s: d) returns (y: int)
{
  y := s.id(1);
}
