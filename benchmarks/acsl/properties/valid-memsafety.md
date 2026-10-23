Consists of three subproperties that are checked simultaneously:
- valid-deref
- valid-free
- valid-memtrack

_Agreement:_
All programs in category 'MemorySafety' either satisfy all subproperties
or violate exactly one subproperty p (p in {valid-free, valid-deref, valid-memtrack})
that is reachable from the program entry.
We ignore further property violations on a path after finding the first violation
(because the behavior may be undefined after the first violation).
