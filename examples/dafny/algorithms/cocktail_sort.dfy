// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/cocktail_sort.dfy
// cocktail shaker sort: each outer iteration runs a forward bubble pass over [lo, hi), which moves the maximum to
// hi - 1, and a backward pass over (lo, hi - 1], which moves the minimum to lo; the backward pass uses two pointers
// j and p == j - 1 (insertion_sort2.dfy)
//
// status: open; the approach closed the goal in exactly one run (a wrong postcondition left a goal), and leaves the
// whole goal in every later run of the same file and jar: the summary lemma current_results_shake does not fire,
// since its fourth side condition, the exit of the forward pass invs(for ks, js check k, j :: n <= j + k + 1), is
// not matched against the fact of that shape, invs(for ⌊K⌋, ⌊Lo⌋, ⌊Hi⌋, J? check k, lo, hi, j :: n <= j + k + 1), not
// even alone, with explicit dependencies, or with the variable renamed (the same condition works in bubble_sort.dfy,
// whose fact has one dependency fewer); an alternative that abstracts each fragment by an atom (currents, passes,
// counters, exits, tests, as consts_prefix of teq.dfy does), so that the summary takes atoms as side conditions,
// fails differently: the definition lemma of the exit, whose left-hand side is a bare comparison n <= j + k + 1,
// matches every comparison fact with the dependency js synthesized as a map (2 k + 1 < n, 0 <= integer(nn), the
// inner constraints), and the atom for the inner counter consumes the fragment K == counter(0, 1, nn) before
// invs_sums_counter needs it as a side condition (NOTES.md); the approach as it stands:
// two inner loops per outer iteration: the forward pass is bubble_pass of bubble_sort.dfy from the previous value to
// an intermediate result (the sequence B?₄₀), the backward pass bubble_pass_back over the two counters j and p from
// the intermediate result to the result (B?₄₈), all as fragments of the iteration constraint of the outer loop; the
// summary lemma current_results_shake takes the fragments of both inner loops as side conditions (bubble_sort.dfy,
// insertion_sort2.dfy) and makes the outer trace the trace of shake(b, k, n), an abstract function; the initial
// values n - k - 2 and n - k - 3 of the backward counters are higher-order X(k) and Y(k) in the side conditions, with
// their values as closed invs side conditions that the simplifier decides, since a pattern sum of a rule variable
// and a bound variable with several summands is not matched (TODO.md); sorted(b, 0, n) follows from the induction
// sorted_shaken_steps over the invariant shaken(b, k, n) indexed by the iteration (both ends sorted, like bubbled in
// bubble_sort.dfy), perm(b, a) from perm_steps and perm_shake

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
lemma {:rw} current_results_shake(a: array<int, int>, n: int, n2: int, n3: int, d: int, ks: List<int>,
                                  bs: List<array<int, int>>, Bs: List<Trace<array<int, int>>>, cs: List<array<int, int>>,
                                  Cs: List<Trace<array<int, int>>>, Js: List<Trace<int>>, Ns: List<Nat>, js: List<int>,
                                  Js2: List<Trace<int>>, Ps: List<Trace<int>>, Ns2: List<Nat>, Js3: List<Trace<int>>,
                                  ps: List<int>, Ps3: List<Trace<int>>, js4: List<int>, Js4: List<Trace<int>>,
                                  js5: List<int>, Js5: List<Trace<int>>, X: int -> int, Y: int -> int)
  // the first pass: from the previous value x to the intermediate result c, over the counter J from k
  requires invs(for ks, cs, Cs check k, c, C :: c == current(C))
  requires invs(for ks, ⌊results(a, ks, bs)⌋, Cs, Js check k, x, C, J :: C == bubble_pass(x, ⌊J⌋))
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(k, 1, nn))
  requires invs(for ks, js check k, j :: n <= j + k + 1)
  requires invs(for ks, Js2 check k, J :: invs(for ⌊J⌋ check j :: j + k + 1 < n2))
  requires Js2 == Js && n2 == n
  requires invs(for ks, js5, Js5 check k, j, J :: j == current(J))
  requires js5 == js && Js5 == Js
  // the second pass: from the intermediate result c to the result b, over the counters J' from n - k - 2 and
  // P' from n - k - 3 down by 1
  requires invs(for ks, bs, Bs check k, b, B :: b == current(B))
  requires invs(for ks, cs, Bs, Js3, Ps3 check k, c, B, J, P :: B == bubble_pass_back(c, ⌊J⌋, ⌊P⌋))
  requires invs(for ks, Ns2, Js3 check k, nn, J :: J == counter(X(k), d, nn))
  requires d == -1
  requires invs(for ks check k :: X(k) == n - k - 2)
  requires invs(for ks, Ns2, Ps check k, nn, P :: P == counter(Y(k), d, nn))
  requires Ps == Ps3
  requires invs(for ks check k :: Y(k) == n - k - 3)
  requires invs(for ks, Js4 check k, J :: invs(for ⌊J⌋ check j :: k < j))
  requires Js4 == Js3
  requires invs(for ks, js4 check k, j :: j <= k)
  requires invs(for ks, ps, Ps3 check k, p, P :: p == current(P))
  requires invs(for ks, js4, Js3 check k, j, J :: j == current(J))
  ensures current(results(a, ks, bs)) == current(trace(a, for ks do b, k :: shake(b, k, n)))

// the invariant after k iterations: the prefix b[0..k) and the suffix b[n - k..n) are sorted, and all of the prefix
// are at most all of the middle, which are at most all of the suffix; the whole range once 2 k + 1 >= n
function shaken(b: array<int, int>, k: int, n: int): bool

// a shake extends both sorted ends by one position
lemma {:rw} shaken_shake(b: array<int, int>, k: int, n: int)
  requires shaken(b, k, n)
  ensures shaken(shake(b, k, n), k + 1, n) <==> true

// the induction: m shakes sort b[0..n) if n <= 2 m + 1
lemma {:rw} sorted_shaken_steps(a: array<int, int>, n: int, m: Nat, F: (array<int, int>, int) -> array<int, int>)
  requires n <= 2 * integer(m) + 1
  requires forall b: array<int, int>, k: int :: 0 <= k < integer(m) && shaken(b, k, n) ==> shaken(F(b, k), k + 1, n)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋ do b, k :: F(b, k))), 0, n) <==> true

// a shake is a permutation, and a trace of steps that preserve the permutation (bubble_sort.dfy)
lemma {:rw} perm_shake(b: array<int, int>, c: array<int, int>, k: int, n: int)
  ensures perm(shake(b, k, n), c) <==> perm(b, c)

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
