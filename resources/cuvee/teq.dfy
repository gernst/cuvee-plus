// the lemma database of -teq, which is injected at the beginning of its output:
// the type of traces and the functions on them (see cuvee.core.Sort.trace and cuvee.core.Fun.trace),
// which exist only with -teq, and lemmas about them, which are rewrite rules of the simplifier ({:rw}),
// the simplifier is expected to prove the goals of -teq on its own, not the solvers,
// functions that produce traces are plural (sums, counts), their scalar counterparts singular (sum, count),
// the lemmas are grouped by the function of their left-hand side

// the type and the functions of Fun.trace, whose type parameters and formals are numbered as there (Fun.formals)

// the traces of trace equation systems, the values of a variable at the loop head
type {:teq} Trace<a₀>
// all but the last element of a trace, written ⌊X⌋
function {:teq} butlast<a₀>(x₀: Trace<a₀>): seq<a₀>
// counter(i, c, n) is the trace i, i + c, ..., i + n c of n steps
function {:teq} counter(x₀: int, x₁: int, x₂: int): Trace<int>
// the last element of a trace
function {:teq} current<a₀>(x₀: Trace<a₀>): a₀
// the elements of sequences
function {:teq} earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀

// the first k elements of a sequence
function {:teq} prefix<a>(k: int, xs: seq<a>): seq<a>

// whether x occurs in a sequence, and the index of its last occurrence (unspecified otherwise)
function {:teq} occurs<a>(x: a, xs: seq<a>): bool
function {:teq} indexof<a>(x: a, xs: seq<a>): int

// whether a sequence has no duplicates
function {:teq} distincts<a>(xs: seq<a>): bool

// consts(n, v) is the trace v, ..., v of n steps
function {:teq} consts<a>(n: int, v: a): Trace<a>

// selects(a, keys) are the values of a at the keys,
// stores(a, keys, values) is the trace of the successive stores of the values at the keys into a
function {:teq} selects<a, b>(a: array<a, b>, keys: seq<a>): seq<b>
function {:teq} stores<a, b>(a: array<a, b>, keys: seq<a>, values: seq<b>): Trace<array<a, b>>

// shifts(a, keys, d) is the trace of the successive copies a[k] := a[k + d] for the keys,
// which is modeled for increasing keys and nonnegative offsets only, where the entries read are not yet modified
function {:teq} shifts(a: array<int, int>, keys: seq<int>, d: int): Trace<array<int, int>>

// the prefix sums of a sequence starting with an initial value, and the sum of a sequence
function {:teq} sums(x: int, values: seq<int>): Trace<int>
function {:teq} sum(values: seq<int>): int

// the prefix parities (the number of even minus the number of odd elements) starting with an initial value,
// and the parity of a sequence
function {:teq} parities(x: int, values: seq<int>): Trace<int>
function {:teq} parity(values: seq<int>): int

// the prefix maxima and minima starting with an initial value
function {:teq} maxs(x: int, values: seq<int>): Trace<int>
function {:teq} mins(x: int, values: seq<int>): Trace<int>

function {:teq} max(m: int, n: int): int
{
  if m <= n then n else m
}

function {:teq} min(m: int, n: int): int
{
  if m <= n then m else n
}

// the number of occurrences of a value, counted from an initial value, and in a sequence
function {:teq} counts<a>(x: int, e: a, vs: seq<a>): Trace<int>
function {:teq} count<a>(e: a, vs: seq<a>): int

// auxiliary predicates, declared only: abstractions of iteration constraints, which lemmas instantiate at witnesses,
// since a side condition that is an iteration constraint does not terminate; named apart from the predicates that
// inputs declare with other meanings, which would be identified with them if their signatures agreed

// the first n values of xs and ys agree
function {:teq} agree_prefix(n: int, xs: seq<int>, ys: seq<int>): bool
// the first n values of ts exceed their positions
function {:teq} above_iterations(n: int, ts: seq<int>): bool
// powers, which are not unfolded
function {:teq} pow(c: int, n: int): int

// traces

// a variable that is increased by c in each iteration is a counter (example 2.3 of the paper)
lemma {:rw} {:teq} trace_1(i: int, c: int, n: int)
  ensures trace(i, for ⌊counter(0, 1, n)⌋ do x, k :: x + c)
    == counter(i, c, n)

// a variable that keeps its value in each iteration
lemma {:rw} {:teq} trace_2<a>(x: a, i: int, c: int, n: int)
  ensures trace(x, for ⌊counter(i, c, n)⌋ do y, v :: y)
    == consts(n, x)

lemma {:rw} {:teq} trace_3<a, b>(a: array<a, b>, keys: seq<a>, values: seq<b>)
  ensures trace(a, for keys, values do b, k, v :: b[k := v])
    == stores(a, keys, values)

// each key is visited once only if they are distinct, hence b[k] is still the initial value a[k],
// in any context f of the read, which may depend on the other dependencies, but not on the accumulator otherwise
lemma {:rw} {:teq} trace_4<a, b>(a: array<a, b>, keys: seq<a>, fs: seq<b -> b>)
  requires distincts(keys)
  ensures trace(a, for keys, fs do b, k, f :: b[k := f(b[k])])
    == trace(a, for keys, fs do b, k, f :: b[k := f(a[k])])

lemma {:rw} {:teq} trace_5(a: array<int, int>, keys: seq<int>, d: int)
  ensures trace(a, for keys do b, k :: b[k := b[k + d]])
    == shifts(a, keys, d)

lemma {:rw} {:teq} trace_6(x: int, values: seq<int>)
  ensures trace(x, for values do s, v :: s + v)
    == sums(x, values)

lemma {:rw} {:teq} trace_7(x: int, values: seq<int>)
  ensures trace(x, for values do s, v :: case v % 2 == 0 => s + 1 case v % 2 != 0 => s - 1)
    == parities(x, values)

lemma {:rw} {:teq} trace_8(x: int, values: seq<int>)
  ensures trace(x, for values do m, v :: case m < v => v case v <= m => m)
    == maxs(x, values)

lemma {:rw} {:teq} trace_9(x: int, values: seq<int>)
  ensures trace(x, for values do m, v :: case v < m => v case m <= v => m)
    == mins(x, values)

lemma {:rw} {:teq} trace_10<a>(x: int, e: a, vs: seq<a>)
  ensures trace(x, for vs do y, v :: case v == e => y + 1 case v != e => y)
    == counts(x, e, vs)

// on booleans, the guards are the values themselves; the occurrences of false come first,
// since the guard b of the other lemma also matches !b, which counts the occurrences of true among the negations
lemma {:rw} {:teq} trace_11(x: int, bs: seq<bool>)
  ensures trace(x, for bs do y, b :: case !b => y + 1 case b => y)
    == counts(x, false, bs)

lemma {:rw} {:teq} trace_12(x: int, bs: seq<bool>)
  ensures trace(x, for bs do y, b :: case b => y + 1 case !b => y)
    == counts(x, true, bs)

// two cases whose results agree under the guard of the second one, x == c, which the simplifier has substituted
// into it, are one; the second result is a variable d, since F(c) would be compared literally
// (from copysome1-1, copysome1-2)
lemma {:rw} {:teq} trace_13(x0: int, n: int, c: int, d: int, F: (int) -> int)
  requires d == F(c)
  ensures trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x != c => F(x) case x == c => d)
    == trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: F(x))

// the same with the guards in the other order
// (from brs1, brs1f, ifcomp, ms1, ms1f)
lemma {:rw} {:teq} trace_14(x0: int, n: int, c: int, d: int, F: (int) -> int)
  requires d == F(c)
  ensures trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x == c => d case x != c => F(x))
    == trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: F(x))

// stores at the positions 0, ..., n - 1 of values read from the array itself outside of that range read the initial
// array
// (from standard_palindrome_ground)
lemma {:rw} {:teq} trace_15(a0: array<int, int>, n: int, hs: seq<int>, F: (int, int) -> int)
  requires invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: n <= F(k, h))
  ensures trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: a[k := a[F(k, h)]])
    == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: a0[F(k, h)]))

// maps

lemma {:rw} {:teq} maps_1<a>(x: a, i: int, c: int, n: int)
  ensures maps(for ⌊counter(i, c, n)⌋ yield v :: x)
    == ⌊consts(n, x)⌋

lemma {:rw} {:teq} maps_2<a>(n: int, xs: seq<a>)
  ensures maps(for ⌊counter(0, 1, n)⌋ yield k :: earlier(k, xs))
    == xs

lemma {:rw} {:teq} maps_3(a: int, b: int, i: int, c: int, n: int)
  ensures maps(for ⌊counter(i, c, n)⌋ yield v :: a + b * v)
    == ⌊counter(a + b * i, b * c, n)⌋

lemma {:rw} {:teq} maps_4<a, b>(a: array<a, b>, keys: seq<a>)
  ensures maps(for keys yield k :: a[k])
    == selects(a, keys)

// invs

lemma {:rw} {:teq} invs_1(b: bool, i: int, c: int, n: int)
  ensures invs(for ⌊counter(i, c, n)⌋ check v :: b)
    <==> n == 0 || b

lemma {:rw} {:teq} invs_2(m: int, i: int, c: int, n: int)
  ensures invs(for ⌊counter(i, c, n)⌋ check k :: m <= k)
    <==> n == 0 || m <= i && m <= i + (n - 1) * c

lemma {:rw} {:teq} invs_3(m: int, i: int, c: int, n: int)
  ensures invs(for ⌊counter(i, c, n)⌋ check k :: k < m)
    <==> n == 0 || i < m && i + (n - 1) * c < m

// a counter by 1 or -1 avoids m if m lies outside of its range, e.g. for loops i != N
lemma {:rw} {:teq} invs_4(m: int, i: int, n: int)
  ensures invs(for ⌊counter(i, 1, n)⌋ check k :: k != m)
    <==> m < i || i + n <= m

lemma {:rw} {:teq} invs_5(m: int, i: int, n: int)
  ensures invs(for ⌊counter(i, -1, n)⌋ check k :: k != m)
    <==> i < m || m <= i - n

// the same counter is increasing for 0 < c, hence an upper bound B holds at all its values before the current one
// iff it holds at the last of them
// (from Mono1_1-2)
lemma {:rw} {:teq} invs_6(x0: int, n: int, b: int, c: int, B: int)
  requires x0 <= b && 0 < c
  ensures
    invs(for ⌊counter(0, 1, n)⌋, ⌊trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x < b => x + 1 case b <= x => x + c)⌋
         check k, x :: x < B)
      <==> (n == 0 || (if n - 1 <= b - x0 then x0 + n - 1 else b + (n - 1 - (b - x0)) * c) < B)

// a lower bound of the values x of a counter with an arbitrary step holds in all iterations iff it holds at both
// ends, since the values are linear; for a counter as the third of three dependencies, with the bound as 0 < x + c,
// since b < x does not match k < x + n (see TODO.md)
// (from benchmark04_conjunctive, benchmark09_conjunctive)
lemma {:rw} {:teq} invs_7(i: int, d: int, n: int, c: int, hs: seq<int>, gs: seq<int>)
  ensures invs(for hs, gs, ⌊counter(i, d, n)⌋ check h, g, x :: 0 < x + c)
    <==> (n == 0 || 0 < i + c && 0 < i + (n - 1) * d + c)

// the same for a counter as the second of three dependencies
// (from benchmark09_conjunctive)
lemma {:rw} {:teq} invs_8(i: int, d: int, n: int, c: int, hs: seq<int>, gs: seq<int>)
  ensures invs(for hs, ⌊counter(i, d, n)⌋, gs check h, x, g :: 0 < x + c)
    <==> (n == 0 || 0 < i + c && 0 < i + (n - 1) * d + c)

// an iteration constraint that is a negated disjunction, as the test of a break, is two of them
// (from benchmark09_conjunctive)
lemma {:rw} {:teq} invs_9(hs: seq<int>, gs: seq<int>, fs: seq<int>, P: (int, int, int) -> bool,
                          Q: (int, int, int) -> bool)
  ensures invs(for hs, gs, fs check h, g, f :: !(P(h, g, f) || Q(h, g, f)))
    <==> invs(for hs, gs, fs check h, g, f :: !P(h, g, f)) && invs(for hs, gs, fs check h, g, f :: !Q(h, g, f))

// two sequences that are equal at the iterations 0, ..., n - 1 agree there
// (from standard_compare_ground)
lemma {:rw} {:teq} invs_10(n: int, xs: seq<int>, ys: seq<int>, hs: seq<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(k, xs) == earlier(k, ys)) <==> agree_prefix(n, xs, ys)

// a search: the elements before the exit n differ from e, i.e., e does not occur in the prefix of length n
// (from standard_find_ground-1)
lemma {:rw} {:teq} invs_11(n: int, e: int, xs: seq<int>, hs: seq<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(k, xs) != e) <==> !occurs(e, prefix(n, xs))

// the values of the iterations exceed the iterations
// (from simple_array_index_value_2)
lemma {:rw} {:teq} invs_12(n: int, ts: seq<int>, hs: seq<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, ts check k, h, t :: k < t) <==> above_iterations(n, ts)

// current

lemma {:rw} {:teq} current_1(i: int, c: int, n: int)
  ensures current(counter(i, c, n))
    == i + n * c

lemma {:rw} {:teq} current_2<a>(x: a, y: a, i: int, c: int, n: int)
  ensures current(trace(x, for ⌊counter(i, c, n)⌋ do z, v :: y))
    == if n == 0 then x else y

lemma {:rw} {:teq} current_3<a>(n: int, x: a)
  ensures current(consts(n, x))
    == x

lemma {:rw} {:teq} current_4<a>(a: array<a, int>, k: a, values: seq<int>)
  ensures current(trace(a, for values do b, v :: b[k := b[k] + v]))
    == a[k := a[k] + sum(values)]

lemma {:rw} {:teq} current_5(x: int, values: seq<int>)
  ensures current(sums(x, values))
    == x + sum(values)

lemma {:rw} {:teq} current_6(x: int, values: seq<int>)
  ensures current(parities(x, values))
    == x + parity(values)

lemma {:rw} {:teq} current_7(x: int, i: int, c: int, n: int)
  ensures current(maxs(x, ⌊counter(i, c, n)⌋))
    == if n == 0 then x else max(x, max(i, i + (n - 1) * c))

lemma {:rw} {:teq} current_8(x: int, y: int, n: int)
  ensures current(maxs(x, ⌊consts(n, y)⌋))
    == if n == 0 then x else max(x, y)

lemma {:rw} {:teq} current_9(x: int, i: int, c: int, n: int)
  ensures current(mins(x, ⌊counter(i, c, n)⌋))
    == if n == 0 then x else min(x, min(i, i + (n - 1) * c))

lemma {:rw} {:teq} current_10(x: int, y: int, n: int)
  ensures current(mins(x, ⌊consts(n, y)⌋))
    == if n == 0 then x else min(x, y)

lemma {:rw} {:teq} current_11<a>(x: int, e: a, vs: seq<a>)
  ensures current(counts(x, e, vs))
    == x + count(e, vs)

// a counter in two phases: by 1 up to the bound b, from an initial value up to b, then by c >= 0, which keeps it
// at least b
// (from Mono1_1-2, phases_1-1, phases_1-2)
lemma {:rw} {:teq} current_12(x0: int, n: int, b: int, c: int)
  ensures if x0 <= b && 0 <= c
    then current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x < b => x + 1 case b <= x => x + c))
           == if n <= b - x0 then x0 + n else b + (n - (b - x0)) * c

// a follower: y increases by 1 whenever it does not exceed the value x of a counter with step 1, hence y is the
// larger of its initial value and the final value of x, given that it starts at least at x
// (from benchmark05_conjunctive)
lemma {:rw} {:teq} current_13(y0: int, x0: int, n: int)
  ensures if x0 <= y0
    then current(trace(y0, for ⌊counter(0, 1, n)⌋, ⌊counter(x0, 1, n)⌋ do y, k, x :: case y <= x => y + 1 case x < y => y))
           == if x0 + n <= y0 then y0 else x0 + n

// a flag, initially x0, that is set to c whenever D holds, is x0 at the end iff D never held, otherwise c
// (from standard_compare_ground)
lemma {:rw} {:teq} current_14(x0: int, c: int, n: int, hs: seq<int>, D: (int, int) -> bool)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do f, k, h :: case D(k, h) => c case !D(k, h) => f))
    == if invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: !D(k, h)) then x0 else c

// a value multiplied by c in each iteration, a geometric sequence
// (from underapprox_1-1, underapprox_1-2)
lemma {:rw} {:teq} current_15(x0: int, c: int, n: int)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: c * x)) == x0 * pow(c, n)

// a value whose two increments are multiples of m keeps its remainder modulo m, a modular invariant
// (from loopv1)
lemma {:rw} {:teq} current_16(x0: int, n: int, a: int, b: int, m: int, hs: seq<int>, C: (int) -> bool)
  requires 0 < m && a % m == 0 && b % m == 0
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h :: case C(h) => x + a case !C(h) => x + b)) % m
    == x0 % m

// a sum that is set to c in the first iteration and adds G(i) in the others is c plus the sum of G over 1, ..., n - 1,
// stated as G(k + 1) over 0, ..., n - 2, since the context of a map knows the range of counter(0, 1, n) only
// (from brs1, brs1f, ms1, ms1f)
lemma {:rw} {:teq} current_17(x0: int, n: int, c: int, G: (int) -> int)
  ensures
    current(trace(x0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do x, k, i :: case i == 0 => c case i != 0 => G(i) + x))
      == if n == 0 then x0 else c + sum(maps(for ⌊counter(0, 1, n - 1)⌋ yield k :: G(k + 1)))

// earlier

lemma {:rw} {:teq} earlier_1(k: int, i: int, c: int, n: int)
  ensures earlier(k, ⌊counter(i, c, n)⌋)
    == i + k * c

lemma {:rw} {:teq} earlier_2<a>(x: a, xs: seq<a>)
  requires occurs(x, xs)
  ensures earlier(indexof(x, xs), xs)
    == x

lemma {:rw} {:teq} earlier_3<a>(k: int, n: int, x: a)
  ensures earlier(k, ⌊consts(n, x)⌋)
    == x

lemma {:rw} {:teq} earlier_4<a, b>(j: int, a: array<a, b>, keys: seq<a>)
  ensures earlier(j, selects(a, keys))
    == a[earlier(j, keys)]

lemma {:rw} {:teq} earlier_5(j: int, x: int, values: seq<int>)
  ensures earlier(j, ⌊sums(x, values)⌋)
    == x + sum(prefix(j, values))

lemma {:rw} {:teq} earlier_6<a>(j: int, x: int, e: a, vs: seq<a>)
  ensures earlier(j, ⌊counts(x, e, vs)⌋)
    == x + count(e, prefix(j, vs))

lemma {:rw} {:teq} earlier_7<a>(j: int, k: int, xs: seq<a>)
  ensures earlier(j, prefix(k, xs))
    == earlier(j, xs)

// agreeing sequences are equal at each position in the range; the atom is the left-hand side
// (from standard_compare_ground)
lemma {:rw} {:teq} earlier_8(n: int, j: int, xs: seq<int>, ys: seq<int>)
  requires agree_prefix(n, xs, ys) && 0 <= j < n
  ensures (earlier(j, xs) == earlier(j, ys)) <==> true

// which is instantiated at the positions j in that range
// (from standard_find_ground-1)
lemma {:rw} {:teq} earlier_9(n: int, j: int, e: int, xs: seq<int>)
  requires !occurs(e, prefix(n, xs)) && 0 <= j < n
  ensures (earlier(j, xs) == e) <==> false

// prefix

lemma {:rw} {:teq} prefix_1(k: int, i: int, c: int, n: int)
  ensures prefix(k, ⌊counter(i, c, n)⌋)
    == ⌊counter(i, c, k)⌋

lemma {:rw} {:teq} prefix_2<a>(k: int, n: int, x: a)
  ensures prefix(k, ⌊consts(n, x)⌋)
    == ⌊consts(k, x)⌋

lemma {:rw} {:teq} prefix_3<a, b>(k: int, a: array<a, b>, keys: seq<a>)
  ensures prefix(k, selects(a, keys))
    == selects(a, prefix(k, keys))

lemma {:rw} {:teq} prefix_4<a, b>(k: int, a: array<a, b>, keys: seq<a>, values: seq<b>)
  ensures prefix(k, ⌊stores(a, keys, values)⌋)
    == ⌊stores(a, prefix(k, keys), prefix(k, values))⌋

lemma {:rw} {:teq} prefix_5(k: int, x: int, values: seq<int>)
  ensures prefix(k, ⌊sums(x, values)⌋)
    == ⌊sums(x, prefix(k, values))⌋

lemma {:rw} {:teq} prefix_6(k: int, x: int, values: seq<int>)
  ensures prefix(k, ⌊maxs(x, values)⌋)
    == ⌊maxs(x, prefix(k, values))⌋

lemma {:rw} {:teq} prefix_7(k: int, x: int, values: seq<int>)
  ensures prefix(k, ⌊mins(x, values)⌋)
    == ⌊mins(x, prefix(k, values))⌋

lemma {:rw} {:teq} prefix_8<a>(k: int, x: int, e: a, vs: seq<a>)
  ensures prefix(k, ⌊counts(x, e, vs)⌋)
    == ⌊counts(x, e, prefix(k, vs))⌋

lemma {:rw} {:teq} prefix_9<a>(xs: seq<a>)
  ensures prefix(0, xs)
    == []

lemma {:rw} {:teq} prefix_10<a>(j: int, k: int, xs: seq<a>)
  ensures prefix(j, prefix(k, xs))
    == prefix(j, xs)

// occurs

// a value read at one of the keys occurs among the values read at them
lemma {:rw} {:teq} occurs_1<a, b>(k: a, a: array<a, b>, keys: seq<a>)
  requires occurs(k, keys)
  ensures occurs(a[k], selects(a, keys))

// a value at an index occurs in the sequence, e.g. a stored value, which current(stores(a, keys, values))[k] reads
// as earlier(indexof(k, keys), values) if k occurs among the keys; the indices of earlier are valid by construction
lemma {:rw} {:teq} occurs_2<a>(j: int, xs: seq<a>)
  ensures occurs(earlier(j, xs), xs)

lemma {:rw} {:teq} occurs_3(j: int, i: int, n: int)
  ensures occurs(j, ⌊counter(i, 1, n)⌋)
    <==> i <= j < i + n

lemma {:rw} {:teq} occurs_4(j: int, i: int, n: int)
  ensures occurs(j, ⌊counter(i, -1, n)⌋)
    <==> i - n < j <= i

lemma {:rw} {:teq} occurs_5<a>(x: a, n: int, y: a)
  ensures occurs(x, ⌊consts(n, y)⌋)
    <==> n != 0 && x == y

lemma {:teq} occurs_6<a>(x: a, k: int, xs: seq<a>)
  requires occurs(x, prefix(k, xs))
  ensures occurs(x, xs)

// j occurs among the values of a counter with a positive step d iff it is in the range and a multiple of d from the
// initial value (teq.dfy has this for the step 1)
// (from array_monotonic)
lemma {:rw} {:teq} occurs_7(i: int, d: int, n: int, j: int)
  requires 0 < d
  ensures occurs(j, ⌊counter(i, d, n)⌋) <==> i <= j < i + n * d && (j - i) % d == 0

// indexof

lemma {:rw} {:teq} indexof_1(j: int, i: int, n: int)
  requires i <= j < i + n
  ensures indexof(j, ⌊counter(i, 1, n)⌋)
    == j - i

lemma {:rw} {:teq} indexof_2(j: int, i: int, n: int)
  requires i - n < j <= i
  ensures indexof(j, ⌊counter(i, -1, n)⌋)
    == i - j

// distincts

lemma {:rw} {:teq} distincts_1(i: int, c: int, n: int)
  requires c != 0
  ensures distincts(⌊counter(i, c, n)⌋)

lemma {:teq} distincts_2<a>(k: int, xs: seq<a>)
  requires distincts(xs)
  ensures distincts(prefix(k, xs))

// length

// the length of the iterations of a counter
// (from sumt2)
lemma {:rw} {:teq} counter_1(i: int, c: int, n: int)
  requires 0 <= n
  ensures |⌊counter(i, c, n)⌋| == n

// selects

lemma {:rw} {:teq} selects_1<a, b>(a: array<a, b>, keys: seq<a>, values: seq<b>)
  requires distincts(keys)
  ensures selects(current(stores(a, keys, values)), keys)
    == values

lemma {:rw} {:teq} selects_2(a: array<int, int>, n: int, i: int, d: int)
  requires 0 <= d
  ensures selects(current(shifts(a, ⌊counter(i, 1, n)⌋, d)), ⌊counter(i, 1, n)⌋)
    == selects(a, ⌊counter(i + d, 1, n)⌋)

// the elements of stores at the positions of a counter, read at the positions of the same counter, are the stored
// values; both counters are patterns, since they are different trace variables in programs
// (from conda, condaf, ss1, ss1f)
lemma {:rw} {:teq} selects_3(a: array<int, int>, i: int, c: int, n: int, vs: seq<int>)
  requires c != 0
  ensures selects(current(stores(a, ⌊counter(i, c, n)⌋, vs)), ⌊counter(i, c, n)⌋) == vs

// array selects

lemma {:rw} {:teq} current_18<a, b>(k: a, a: array<a, b>, keys: seq<a>, values: seq<b>)
  ensures current(stores(a, keys, values))[k]
    == if occurs(k, keys) then earlier(indexof(k, keys), values) else a[k]

// an earlier state reads the value stored last at k among the keys stored so far, the initial value otherwise
// (indexof is the *last* occurrence, hence indexof(k, prefix(j, keys)) <= indexof(k, keys) but not equal)
lemma {:rw} {:teq} earlier_10<a, b>(k: a, j: int, a: array<a, b>, keys: seq<a>, values: seq<b>)
  ensures earlier(j, ⌊stores(a, keys, values)⌋)[k]
    == if occurs(k, prefix(j, keys)) then earlier(indexof(k, prefix(j, keys)), values) else a[k]

lemma {:rw} {:teq} current_19(a: array<int, int>, n: int, i: int, d: int, k: int)
  ensures if 0 <= d
    then current(shifts(a, ⌊counter(i, 1, n)⌋, d))[k]
           == if i <= k < i + n then a[k + d] else a[k]

// stores at the positions of a counter, guarded by C, keep the other positions; a read at j
// (from copysome1-1, copysome1-2)
lemma {:rw} {:teq} current_20(a0: array<int, int>, n: int, j: int, C: (int) -> bool, V: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case C(i) => a[i := V(i)] case !C(i) => a))[j]
      == if 0 <= j < n && C(j) then V(j) else a0[j]

// the same, with the guard and the value on the values of three further dependencies at the iteration of j
// (from array_mul_init)
lemma {:rw} {:teq} current_21(a0: array<int, int>, n: int, j: int, hs: seq<int>, cs: seq<int>, vs: seq<int>,
                              C: (int, int, int) -> bool, V: (int, int, int) -> int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, hs, cs, vs do a, k, h, c, v ::
                  case C(h, c, v) => a[k := V(h, c, v)] case !C(h, c, v) => a))[j]
    == if 0 <= j < n && C(earlier(j, hs), earlier(j, cs), earlier(j, vs))
       then V(earlier(j, hs), earlier(j, cs), earlier(j, vs))
       else a0[j]

// the same, at distinct positions ps, which are kept as matched, read by occurs and indexof
// (from array_monotonic)
lemma {:rw} {:teq} distincts_3(a0: array<int, int>, n: int, j: int, ps: seq<int>, cs: seq<int>, C: (int, int) -> bool,
                               V: (int, int) -> int)
  ensures if distincts(ps)
    then current(trace(a0, for ⌊counter(0, 1, n)⌋, ps, cs do a, k, p, c ::
                         case C(p, c) => a[p := V(p, c)] case !C(p, c) => a))[j]
           == if occurs(j, ps) && C(j, earlier(indexof(j, ps), cs))
              then V(j, earlier(indexof(j, ps), cs))
              else a0[j]

// a clamp of each element to b, where the guard reads the initial element, since each position is written in its own
// iteration only; a generic guard C(a[k], k) is no pattern, and C(a, k) would read other positions
// (from condn, condnf)
lemma {:rw} {:teq} current_22(a0: array<int, int>, n: int, j: int, b: int, hs: seq<int>)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: case a[k] < b => a case b <= a[k] => a[k := b]))[j]
    == if 0 <= j < n && b <= a0[j] then b else a0[j]

// an array filled by a recurrence at the positions 1, ..., n, each element from its predecessor plus G of the position
// of the predecessor, is the initial element plus the sum of G over the positions before
// (from eqn1, eqn1f, nsqm, nsqmf, pcomp, pcompf, sqm)
lemma {:rw} {:teq} current_23(b0: array<int, int>, n: int, j: int, G: (int) -> int)
  ensures current(trace(b0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do b, k, i :: b[i := G(k) + b[k]]))[j]
    == if 0 <= j <= n then b0[0] + sum(maps(for ⌊counter(0, 1, j)⌋ yield k :: G(k))) else b0[j]

// the same with two added terms, since a higher-order summand matches a single summand only (see TODO.md)
// (from nsqm, nsqmf, pcomp, pcompf, sqm)
lemma {:rw} {:teq} current_24(b0: array<int, int>, n: int, j: int, G: (int) -> int, H: (int) -> int)
  ensures current(trace(b0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do b, k, i :: b[i := b[k] + G(k) + H(k)]))[j]
    == if 0 <= j <= n then b0[0] + sum(maps(for ⌊counter(0, 1, j)⌋ yield k :: G(k) + H(k))) else b0[j]

// the special case of a constant added term
// (from standard_seq_init_ground)
lemma {:rw} {:teq} current_25(a0: array<int, int>, n: int, c: int, j: int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do a, k, i :: a[i := a[k] + c]))[j]
    == if 1 <= j <= n then a0[0] + j * c else a0[j]

// sum, which is linear, and the linear transformations are moved to the outside

lemma {:rw} {:teq} sum_1()
  ensures sum([])
    == 0

lemma {:rw} {:teq} sum_2(n: int, x: int)
  ensures sum(⌊consts(n, x)⌋)
    == x * n

lemma {:rw} {:teq} sum_3(values: seq<int>)
  ensures sum(maps(for values yield v :: -v))
    == -sum(values)

lemma {:rw} {:teq} sum_4(values: seq<int>, a: int)
  ensures sum(maps(for values yield v :: a * v))
    == a * sum(values)

lemma {:rw} {:teq} sum_5(xs: seq<int>, ys: seq<int>)
  ensures sum(maps(for xs, ys yield v, w :: v + w))
    == sum(xs) + sum(ys)

// the arithmetic series, which is exact, since n * (n - 1) is even
lemma {:rw} {:teq} sum_6(i: int, c: int, n: int)
  ensures sum(⌊counter(i, c, n)⌋)
    == (2 * i + (n - 1) * c) * n / 2

lemma {:rw} {:teq} distincts_4<a>(a: array<a, int>, k: a, v: int, keys: seq<a>)
  ensures if distincts(keys)
    then sum(selects(a[k := v], keys))
           == if occurs(k, keys) then sum(selects(a, keys)) + v - a[k] else sum(selects(a, keys))

// parity

lemma {:rw} {:teq} distincts_5<a>(a: array<a, int>, k: a, v: int, keys: seq<a>)
  ensures if distincts(keys)
    then parity(selects(a[k := v], keys))
           == if occurs(k, keys)
              then parity(selects(a, keys)) + (if v % 2 == 0 then 1 else -1) - (if a[k] % 2 == 0 then 1 else -1)
              else parity(selects(a, keys))

// count

lemma {:rw} {:teq} count_1<a>(n: int, e: a, v: a)
  ensures count(e, ⌊consts(n, v)⌋)
    == if v == e then n else 0

// an update of a visited key replaces its contribution, as for sum and parity
lemma {:rw} {:teq} distincts_6<a, b>(a: array<a, b>, k: a, w: b, e: b, keys: seq<a>)
  ensures if distincts(keys)
    then count(e, selects(a[k := w], keys))
           == if occurs(k, keys)
              then count(e, selects(a, keys)) + (if w == e then 1 else 0) - (if a[k] == e then 1 else 0)
              else count(e, selects(a, keys))

// the iterations of a counter by 1 before m and from m on, e.g. for loops with if (i < m) in the body
lemma {:rw} {:teq} count_2(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures count(true, maps(for ⌊counter(i, 1, n)⌋ yield k :: k < m))
    == m - i

lemma {:rw} {:teq} count_3(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures count(false, maps(for ⌊counter(i, 1, n)⌋ yield k :: k < m))
    == i + n - m

lemma {:rw} {:teq} count_4(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures count(true, maps(for ⌊counter(i, 1, n)⌋ yield k :: m <= k))
    == i + n - m

lemma {:rw} {:teq} count_5(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures count(false, maps(for ⌊counter(i, 1, n)⌋ yield k :: m <= k))
    == m - i

lemma {:rw} {:teq} count_6<a>(e: a, vs: seq<a>)
  ensures 0 <= count(e, vs)

// the numbers 0, ..., n - 1 with the remainder r modulo m number (n + m - 1 - r) / m
// (from half, sumt2)
lemma {:rw} {:teq} count_7(n: int, m: int, r: int, hs: seq<int>)
  requires 0 <= n && 0 < m && 0 <= r < m
  ensures count(r, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: k % m)) == (n + m - 1 - r) / m

// among the truth values of a map, those that are false are the others than those that are true; the dependencies
// are kept as matched, such that the counts are syntactically equal to those of the program
// (from sumt2)
lemma {:rw} {:teq} count_8(ks: seq<int>, hs: seq<int>, P: (int, int) -> bool)
  ensures count(false, maps(for ks, hs yield k, h :: P(k, h)))
    == |ks| - count(true, maps(for ks, hs yield k, h :: P(k, h)))

// the iterations where a value is r are counted by the occurrences of r among the values
// (from sumt2)
lemma {:rw} {:teq} count_9(ks: seq<int>, r: int, hs: seq<int>, F: (int, int) -> int)
  ensures count(true, maps(for ks, hs yield k, h :: F(k, h) == r))
    == count(r, maps(for ks, hs yield k, h :: F(k, h)))

// bounds

// the initial value is a bound of the prefix maxima and minima, which are attained by some value otherwise
lemma {:rw} {:teq} current_26(x: int, values: seq<int>)
  ensures x <= current(maxs(x, values))

lemma {:rw} {:teq} earlier_11(k: int, x: int, values: seq<int>)
  ensures earlier(k, values) <= current(maxs(x, values))

lemma {:rw} {:teq} current_27(x: int, values: seq<int>)
  ensures current(mins(x, values)) <= x

lemma {:rw} {:teq} current_28(k: int, x: int, values: seq<int>)
  ensures current(mins(x, values)) <= earlier(k, values)

// a value that increases by a positive constant in each of its three cases exceeds its initial value after at
// least one iteration
// (from large_const)
lemma {:rw} {:teq} current_29(x0: int, n: int, a: int, b: int, c: int, hs: seq<int>, C: (int) -> bool,
                              D: (int) -> bool, E: (int) -> bool)
  requires 0 < n && 0 < a && 0 < b && 0 < c
  ensures x0 < current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h ::
    case C(h) => x + a case D(h) => x + b case E(h) => x + c))

// an interval that contains the initial value and that each of the three cases maps into itself contains the
// current value, an inductive invariant; the left-hand side is the conjunction of both bounds, which binds both
// (from benchmark51_polynomial)
lemma {:rw} {:teq} current_30(x0: int, n: int, lo: int, hi: int, C1: (int) -> bool, C2: (int) -> bool,
                              C3: (int) -> bool, F1: (int) -> int, F2: (int) -> int, F3: (int) -> int)
  requires lo <= x0 <= hi
    && (forall y: int :: lo <= y <= hi && C1(y) ==> lo <= F1(y) <= hi)
    && (forall y: int :: lo <= y <= hi && C2(y) ==> lo <= F2(y) <= hi)
    && (forall y: int :: lo <= y <= hi && C3(y) ==> lo <= F3(y) <= hi)
  ensures
    (lo <= current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case C1(x) => F1(x) case C2(x) => F2(x) case C3(x) => F3(x)))
       && current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case C1(x) => F1(x) case C2(x) => F2(x) case C3(x) => F3(x))) <= hi)
      <==> true

// which is instantiated at the positions j in the range
// (from simple_array_index_value_2)
lemma {:rw} {:teq} earlier_12(n: int, j: int, ts: seq<int>)
  requires above_iterations(n, ts) && 0 <= j < n
  ensures (j < earlier(j, ts)) <==> true

// arithmetic, in the normal form of the simplifier

// even summands do not change the remainder modulo 2
// (from array_monotonic, phases_1-1, phases_1-2)
lemma {:rw} {:teq} lemma_1(x: int, n: int)
  ensures (x + 2 * n) % 2 == x % 2

// a positive number divides itself
// (from modn, modnf)
lemma {:rw} {:teq} lemma_2(x: int)
  requires 0 < x
  ensures x % x == 0

// division of a multiple of m plus a remainder below m
// (from half)
lemma {:rw} {:teq} lemma_3(m: int, k: int, r: int)
  requires 0 < m && 0 <= r < m
  ensures (m * k + r) / m == k

// twice a number is the product of consecutive numbers iff it is its half, as an equivalence of atoms, since an
// equation of integers as a lemma rewrites its left-hand side as a term
// (from gauss_sum)
lemma {:rw} {:teq} lemma_4(n: int, s: int)
  ensures (2 * s == n + n * n) <==> (s == (n + n * n) / 2)

// the sum 0 + 1 + ... + (n - 1) plus 1 is at least n
// (from afnp2014)
lemma {:rw} {:teq} lemma_5(n: int)
  ensures n <= (-n + n * n) / 2 + 1

// division by 2 of polynomials with even coefficients, since a generic (2 * a + 2 * b) / 2 does not match literal
// coefficients
// (from eqn1, eqn1f)
lemma {:rw} {:teq} lemma_6(x: int)
  ensures (2 * x + 2 * x * x) / 2 == x + x * x

// the same
// (from nsqm, nsqmf, sqm)
lemma {:rw} {:teq} lemma_7(x: int)
  ensures (4 * x + 2 * x * x) / 2 == 2 * x + x * x

// the same
// (from pcomp, pcompf)
lemma {:rw} {:teq} lemma_8(x: int)
  ensures (6 * x + 6 * x * x) / 2 == 3 * x + 3 * x * x

// the differences (k + 1)^3 - k^3 - 1 = 3 * k + 3 * k * k telescope to n^3 - n; teq.dfy splits such a sum by linearity
// first, hence the sum of 3 * k * k as the rest, such that the division atoms cancel
// (from pcomp, pcompf)
lemma {:rw} {:teq} sum_7(n: int)
  requires 0 <= n
  ensures sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: 3 * k * k)) == n * n * n - n - 3 * ((-n + n * n) / 2)

// a power of 2 is not divisible by 3
// (from underapprox_1-1, underapprox_1-2)
lemma {:rw} {:teq} pow_1(n: int)
  requires 0 <= n
  ensures (pow(2, n) % 3 == 0) <==> false

// a nonnegative factor cancels in a strict comparison; does not match a literal coefficient (see TODO.md)
// (from count_by_k)
lemma {:rw} {:teq} lemma_9(k: int, a: int, b: int)
  requires 0 <= k
  ensures (k * a < k * b) <==> (0 < k && a < b)
