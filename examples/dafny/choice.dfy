// nondeterministic choices are if statements with guard *,
// chains of choices if * { ... } else if * { ... } else { ... } are a single choice
method pick(n: int) returns (k: int)
  requires 0 <= n
  ensures 0 <= k && k <= n
{
  if * {
    k := 0;
  } else if * {
    k := n;
  } else if n < 1 {
    k := n;
  } else {
    k := 1;
  }

  if * {
    assert 0 <= k;
  }
}
