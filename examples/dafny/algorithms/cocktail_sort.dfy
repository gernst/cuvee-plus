// ./Cuvee.sh -teq -entry main -include teq:nested -simplify examples/dafny/algorithms/cocktail_sort.dfy
// cocktail shaker sort: each outer iteration runs a forward bubble pass over [lo, hi), which moves the maximum to
// hi - 1, and a backward pass over (lo, hi - 1], which moves the minimum to lo; the backward pass uses two pointers
// j and p == j - 1 (insertion_sort2.dfy)
//
// status: verified with -teq -simplify, both sorted(b, 0, n) and perm(b, a) (Oct 11, 2026, evening);
// two inner loops per outer iteration: the forward pass is bubble_pass of bubble_sort.dfy from the previous value to
// an intermediate result, the backward pass bubble_pass_back over the two counters j and p from the intermediate
// result to the result, all as fragments of the iteration constraint of the outer loop; the summary lemma
// current_results_shake takes the fragments of both inner loops as side conditions (bubble_sort.dfy,
// insertion_sort2.dfy) and makes the outer trace the trace of shake(b, k, len), an abstract function; the initial
// values len - k - 2 and len - k - 3 of the backward counters are higher-order X(k) and Y(k) in the side conditions,
// with their values as closed invs side conditions that the simplifier decides, since a pattern sum of a rule
// variable and a bound variable with several summands is not matched (TODO.md); sorted(b, 0, len) follows from the
// induction sorted_shaken_steps over the invariant shaken(b, k, len) indexed by the iteration (both ends sorted, like
// bubbled in bubble_sort.dfy), perm(b, a) from perm_steps and perm_shake;
// the goal stayed open for a day for three reasons, found by truncated copies of the summary lemma with the first k
// side conditions (NOTES.md): the last side condition, the final values of the backward counter, had all its
// variables bound by earlier conditions, so it was closed and decided instead of matched against the fact, which
// fails (NOTES.md, principle 9; now fresh variables js6, Js6 with identifying equations, like js5, Js5 for the forward
// pass); the bound len <= 2 m + 1 of the induction is not a difference constraint and the simplifier does not combine
// the facts n <= integer(m) + lo + 1 and lo == integer(m), so the lemma states the bound in the goal's form with lo an
// open variable; and the rule variable n was renamed to len, apart from the program's n (finding 21), which alone did
// not help; the run of Oct 10 that closed the goal once presumably decided the closed condition by chance
function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// the inner counters (fragments.dfy)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// the outer trace: the initial value followed by the results of the second inner loop
function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// one forward pass of bubble sort over the positions js (bubble_sort.dfy)
function {:fold} bubble_pass(b: array<int, int>, js: List<int>): Trace<array<int, int>>
{
  trace(b, for js do x, j :: case x[j + 1] < x[j] => x[j := x[j + 1]][j + 1 := x[j]] case x[j] <= x[j + 1] => x)
}

// one backward pass over the positions js and ps == js - 1: adjacent elements out of order are swapped
function {:fold} bubble_pass_back(b: array<int, int>, js: List<int>, ps: List<int>): Trace<array<int, int>>
{
  trace(b, for js, ps do x, j, p :: case x[j] < x[p] => x[j := x[p]][p := x[j]] case x[p] <= x[j] => x)
}

// the pass of iteration k of cocktail sort: a forward pass over k, ..., n - k - 2, then a backward pass over
// n - k - 2, ..., k + 1
function shake(b: array<int, int>, k: int, n: int): array<int, int>

// the summary of the two inner loops: in iteration k, the result is the shake of the previous value, given the trace
// equations and iteration constraints of both inner loops as side conditions (bubble_sort.dfy, insertion_sort2.dfy)
lemma {:rw} current_results_shake(a: array<int, int>, len: int, len2: int, len3: int, d: int, ks: List<int>,
                                  bs: List<array<int, int>>, Bs: List<Trace<array<int, int>>>, cs: List<array<int, int>>,
                                  Cs: List<Trace<array<int, int>>>, Js: List<Trace<int>>, Ns: List<Nat>, js: List<int>,
                                  Js2: List<Trace<int>>, Ps: List<Trace<int>>, Ns2: List<Nat>, Js3: List<Trace<int>>,
                                  ps: List<int>, Ps3: List<Trace<int>>, js4: List<int>, Js4: List<Trace<int>>,
                                  js5: List<int>, Ns5: List<Nat>, js6: List<int>, Ns6: List<Nat>, Ns7: List<Nat>, X: int -> int, Y: int -> int)
  // the first pass: from the previous value x to the intermediate result c, over the counter J from k
  requires invs(for ks, cs, Cs check k, c, C :: c == current(C))
  requires invs(for ks, ⌊results(a, ks, bs)⌋, Cs, Js check k, x, C, J :: C == bubble_pass(x, ⌊J⌋))
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(k, 1, nn))
  requires invs(for ks, js check k, j :: len <= j + k + 1)
  requires invs(for ks, Js2 check k, J :: invs(for ⌊J⌋ check j :: j + k + 1 < len2))
  requires Js2 == Js && len2 == len
  // the final values of the forward counter in the form that the module nested gives them (without the module the
  // fragment is j == current(J), and the summary was stated with it)
  requires invs(for ks, Ns5, js5 check k, nn, j :: j == integer(nn) + k)
  requires js5 == js && Ns5 == Ns
  // the second pass: from the intermediate result c to the result b, over the counters J' from len - k - 2 and
  // P' from len - k - 3 down by 1
  requires invs(for ks, bs, Bs check k, b, B :: b == current(B))
  requires invs(for ks, cs, Bs, Js3, Ps3 check k, c, B, J, P :: B == bubble_pass_back(c, ⌊J⌋, ⌊P⌋))
  requires invs(for ks, Ns2, Js3 check k, nn, J :: J == counter(X(k), d, nn))
  requires d == -1
  requires invs(for ks check k :: X(k) == len - k - 2)
  requires invs(for ks, Ns2, Ps check k, nn, P :: P == counter(Y(k), d, nn))
  requires Ps == Ps3
  requires invs(for ks check k :: Y(k) == len - k - 3)
  requires invs(for ks, Js4 check k, J :: invs(for ⌊J⌋ check j :: k < j))
  requires Js4 == Js3
  requires invs(for ks, js4 check k, j :: j <= k)
  // the final values of the backward counters in the module's forms, p == len - k - 3 - nn and j == len - k - 2 - nn
  requires invs(for ks, Ns6, ps check k, nn, p :: integer(nn) + p + k + 3 == len)
  requires Ns6 == Ns2
  // the final values of the backward counter J' with fresh variables, matched against the fact, then identified: with
  // js4 and Js3 bound by the conditions above, the condition is closed and decided instead, which fails (the first
  // condition that fails, found by the truncated copies cock7_*; the same condition for the forward pass, js5 and
  // Js5, uses fresh variables)
  requires invs(for ks, Ns7, js6 check k, nn, j :: integer(nn) + j + k + 2 == len)
  requires js6 == js4 && Ns7 == Ns2
  ensures current(results(a, ks, bs)) == current(trace(a, for ks do b, k :: shake(b, k, len)))

// the invariant after k iterations: the prefix b[0..k) and the suffix b[n - k..n) are sorted, and all of the prefix
// are at most all of the middle, which are at most all of the suffix; the whole range once 2 k + 1 >= n
function shaken(b: array<int, int>, k: int, n: int): bool

// a shake extends both sorted ends by one position
lemma {:rw} shaken_shake(b: array<int, int>, k: int, len: int)
  requires shaken(b, k, len)
  ensures shaken(shake(b, k, len), k + 1, len) <==> true

// the induction: m shakes sort b[0..len) if len <= 2 m + 1
// the counter of the outer loop is the trace variable K of the goal, with K == counter(0, 1, m) as a hypothesis, which
// the open trace variable Kv of the left-hand side picks up (the form with ⌊counter(0, 1, m)⌋ never matches)
// the bound len <= 2 m + 1 is not a difference constraint, and the goal has it as n <= integer(m) + lo + 1 with
// lo == integer(m) as a separate fact, which the simplifier does not combine (NOTES.md, finding 11); so the bound is
// stated in the goal's form, with lo an open variable matched against its equation; the counter as a dependency of
// the combinator matches ⌊K⌋ with K == counter(0, 1, m) in the context (NOTES.md, bubble sort)
lemma {:rw} sorted_shaken_steps(a: array<int, int>, len: int, m: Nat, l: int, F: (array<int, int>, int) -> array<int, int>)
  requires l == integer(m)
  requires len <= integer(m) + l + 1
  requires forall b: array<int, int>, k: int :: 0 <= k < integer(m) && shaken(b, k, len) ==> shaken(F(b, k), k + 1, len)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋ do b, k :: F(b, k))), 0, len) <==> true

// a shake is a permutation, and a trace of steps that preserve the permutation (bubble_sort.dfy)
lemma {:rw} perm_shake(b: array<int, int>, c: array<int, int>, k: int, len: int)
  ensures perm(shake(b, k, len), c) <==> perm(b, c)

lemma {:rw} perm_steps(a: array<int, int>, c: array<int, int>, ks: List<int>, F: (array<int, int>, int) -> array<int, int>)
  requires forall b: array<int, int>, k: int :: perm(F(b, k), b)
  ensures perm(current(trace(a, for ks do b, k :: F(b, k))), c) <==> perm(a, c)

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures sorted(b, 0, n)
  ensures perm(b, a)
{
  var lo: int;
  var hi: int;
  var j: int;
  var p: int;
  var t: int;
  b := a;
  lo := 0;
  hi := n;
  while lo + 1 < hi
  {
    j := lo;
    while j + 1 < hi
    {
      if b[j + 1] < b[j] {
        t := b[j];
        b[j] := b[j + 1];
        b[j + 1] := t;
      }
      j := j + 1;
    }
    hi := hi - 1;
    j := hi - 1;
    p := hi - 2;
    while lo < j
    {
      if b[j] < b[p] {
        t := b[j];
        b[j] := b[p];
        b[p] := t;
      }
      j := j - 1;
      p := p - 1;
    }
    lo := lo + 1;
  }
}
