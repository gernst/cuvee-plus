# Verifying renc with `-vcgen`

Plan (Oct 23, 2026), not implemented: the operations of
[renc.dfy](../resources/cuvee/implement/renc.dfy) get contracts over the original types (`map<a, b>`, `set<a>`),
`-vcgen` turns them into verification conditions, and cvc5 proves them, with a representation invariant that couples
each representation to the abstract value it encodes.

## What a proof can show, and what it cannot

renc is sound by an argument about all runs at once (the shared predicates force the solver to generalize; header
of renc.dfy, [implement.md](implement.md)). Verification conditions are about one execution of one operation.
Hence two parts:

1. **Local refinement, by `-vcgen` and cvc5:** each operation, run on representations coupled to abstract values,
   along the run whose assumed answers are the true ones, yields a representation coupled to the result of the
   abstract operation, returns the true answer where the prophecy matches, asserts only true answers, and admits the
   true value at every nondeterministic choice (bridges of `N`, weak operations).
2. **The global conditions** under which the local refinement implies soundness of the encoding, checked separately
   (syntactically, or as a theorem in Lean): every observation has a run that asserts its answer, the numbering by
   `tick` does not depend on the prophecy, the arguments of `R`, `K`, `S`, `N` tell runs of one execution apart only
   by keys that the asserting run observes as well.

## Steps

1. **Abstract and concrete sorts side by side.** Today the implementing datatype must have the name of the sort it
   implements (`datatype {:implement} map<a, b>`), so inside renc.dfy `map` is the representation and the abstract
   sort is gone. Allow `datatype {:implement map} rmap<a, b>`: the datatype `rmap` implements the sort `map`;
   `-implement` replaces `map` by `rmap` in clients, and inside the module both exist.
2. **Coupling invariants**, one ghost predicate per datatype, over the representation and the abstract value:
   ```dafny
   predicate MapAbs<a, b>(r: rmap<a, b>, m: map<a, b>)
   { (r.last_in <==> r.last_key in m) && (r.last_in ==> r.last == m[r.last_key]) }
   predicate SetAbs<a>(r: rset<a>, s: set<a>)
   { r.last_in <==> r.last_key in s }
   ```
   The sizes are not in the representation: `N(version, z)` stands for `z == |m|` of the abstract value of that
   version (see step 4).
3. **Contracts over the abstract values**, with the abstract inputs as ghost inputs and the abstract result in the
   postcondition:
   ```dafny
   method Get(k: a, ctx: x, ghost m: map<a, b>) returns (v: b)
     requires MapAbs(this, m)
     ensures last_key == k && k in m ==> v == m[k]
   method Put(k: a, v: b, ctx: x, ghost m: map<a, b>) returns (r: rmap<a, b>)
     requires MapAbs(this, m)
     ensures MapAbs(r, m[k := v])
   method Merge(n: rmap<a, b>, ctx: x, ghost m: map<a, b>, ghost m': map<a, b>) returns (r: rmap<a, b>)
     requires MapAbs(this, m) && MapAbs(n, m')
     ensures MapAbs(r, m + m')
   function KeySet(): rset<a>  // ensures SetAbs(KeySet(), m.Keys)
   ```
   likewise for the operations of sets, `Remove`, `ValueSet` (only the constraint at the prophecy element), the weak
   relations (`false` only if the abstract relation is false), and the creations.
4. **The intended meaning of the predicates.** `R`, `K`, `S`, `N` are uninterpreted; the verification conditions
   need their meaning along the run with true answers. An annotation at each observation and bridge states it, e.g.
   `assume {:truth d == (last_key in m')} K(...)`, `assert {:truth v == m[k]} R(...)`,
   `assume {:truth y == |m|} N(version, y)`. A verification mode of `-vcgen` replaces `assume P` by `assume φ` and
   `assert P` by `assert φ`, and turns each nondeterministic choice `w := *; assume B(w)` into the obligation that
   the true value is admissible, `B(truth)`, e.g. `max(|m|, |m'|) <= |m + m'| <= |m| + |m'|` for the bridge of a
   merge, before it continues with `w := truth`.
5. **The global conditions** (part 2 above) as checks over the bodies: equal increments of `tick` on all branches,
   an assertion of the predicate on the branch `last_key == key` of every observation, and the arguments of the
   predicates; first as a syntactic check in `Implement` (with the check of TODO.md that bodies apply no function
   implemented by a method), later as a Lean theorem about the encoding.
6. **Solver input.** `-vcgen -cvc5` on renc.dfy, monomorphic (see the gaps).

## Gaps of the current setup

- **The abstract sort is shadowed** by the implementing datatype (step 1): needs an `{:implement name}` form for
  datatypes and the replacement of the sort in `-implement`.
- **No ghost inputs** in the Dafny frontend (`ghost` is not a keyword). Without them, the abstract values would be
  ordinary inputs, which the check of patterns rejects (a pattern contains all inputs except the context); either
  ghost inputs exempt from the pattern like `{:context ctx}`, or the contracts in a separate harness that wraps
  each operation.
- **Maps reach no solver:** `Fun.map` is not expected to be supported (doc/datastructures.md); cvc5 has sets with
  cardinality, arrays, but no finite maps. Needs a lowering of `map<a, b>` to a set of keys and an array of values
  for cvc5 (`map.get` as `select`, `map.store` as an insertion into the keys and a `store`, `|m|` as the
  cardinality of the keys, `m + n`, `m - s` by quantified definitions). `set.update` and `set.proper_subset` are
  declared but not defined for cvc5 either (TODO.md).
- **The module is polymorphic** (`a`, `b`, and the context `x`), and cvc5 does not accept polymorphic verification
  conditions, while `-monomorph` leaves polymorphic assertions uninstantiated (TODO.md). Either instantiate the
  verification conditions at uninterpreted sorts (a monomorphic copy per operation, sound by parametricity), or
  extend `-monomorph` to assertions.
- **The intended meaning of the predicates** has no syntax yet (step 4): the `{:truth φ}` annotations, and a mode of
  `-vcgen` that uses them, including the obligation of admissible choices.
- **Static predicates and qualified calls:** `set.S` from the map's members resolves by the static members of the
  frontend; `map.N` does not parse (`map` is a keyword), hence `N` is top-level. A renaming of the sorts (step 1)
  would make `rmap.R` and `rset.S` uniform.
- **The global conditions are not checked anywhere** (step 5); today they are argued in comments and guarded by the
  invalid examples of examples/dafny/renc (`invalid_absent`, `invalid_merge`), which found two violations.
- **Side branches** (`assume false`) are fine for `-vcgen` (the weakest precondition of `assume false` is `true`), and
  `-chc` ends paths there since 0.50.13; no gap.
