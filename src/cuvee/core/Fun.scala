package cuvee.core

import util.Name

// functions are equal if their names, signatures, and the names of their formal parameters are, hence the
// declarations of built-in functions in the preludes name the formals as the values below
case class Fun(name: Name, params: List[Param], formals: List[Var], res: Type):
  def args = formals.types
  def arity = formals.length

object Fun:
  import Param.a
  import Param.b
  import Sort.bool

  def formals(types: Type*) =
    Expr.vars("x", types.toList)

  val true_ = Fun("true", Nil, Nil, bool)
  val false_ = Fun("false", Nil, Nil, bool)

  val eq_ = Fun("=", List(a), formals(a, a), bool)
  val ite = Fun("ite", List(a), formals(bool, a, a), a)

  val select = Fun("select", List(a, b), formals(Sort.array(a, b), a), b)
  val store = Fun("store", List(a, b), formals(Sort.array(a, b), a, b), Sort.array(a, b))
  val const = Fun("const", List(a, b), formals(b), Sort.array(a, b))

  // sequences as in cvc5, where seq.empty needs its type, (as seq.empty (Seq a)),
  // seq.extract takes an offset and a length, and seq.update and seq.contains take a subsequence
  object seq:
    val empty = Fun("seq.empty", List(a), Nil, Sort.seq(a))
    val unit = Fun("seq.unit", List(a), formals(a), Sort.seq(a))
    val concat = Fun("seq.++", List(a), formals(Sort.seq(a), Sort.seq(a)), Sort.seq(a))
    val len = Fun("seq.len", List(a), formals(Sort.seq(a)), Sort.int)
    val nth = Fun("seq.nth", List(a), formals(Sort.seq(a), Sort.int), a)
    val update = Fun("seq.update", List(a), formals(Sort.seq(a), Sort.int, Sort.seq(a)), Sort.seq(a))
    val extract = Fun("seq.extract", List(a), formals(Sort.seq(a), Sort.int, Sort.int), Sort.seq(a))
    val contains = Fun("seq.contains", List(a), formals(Sort.seq(a), Sort.seq(a)), bool)
    val prefixof = Fun("seq.prefixof", List(a), formals(Sort.seq(a), Sort.seq(a)), bool)

    // not part of cvc5: the update s[i := v] of a single element, membership x in s, and proper prefixes s < t
    val store = Fun("seq.store", List(a), formals(Sort.seq(a), Sort.int, a), Sort.seq(a))
    val member = Fun("seq.member", List(a), formals(a, Sort.seq(a)), bool)
    val proper = Fun("seq.proper_prefixof", List(a), formals(Sort.seq(a), Sort.seq(a)), bool)

    val all = List(empty, unit, concat, len, nth, update, extract, contains, prefixof, store, member, proper)

  // finite sets as in cvc5, where set.empty needs its type, (as set.empty (Set a)), and member takes the element first
  object set:
    val empty = Fun("set.empty", List(a), Nil, Sort.set(a))
    val singleton = Fun("set.singleton", List(a), formals(a), Sort.set(a))
    // the update s[x := b], which contains x exactly if b, an insertion if b is true, of which set displays are built
    // (see dafny.Parser); not part of cvc5
    val update = Fun("set.update", List(a), formals(Sort.set(a), a, bool), Sort.set(a))
    val union = Fun("set.union", List(a), formals(Sort.set(a), Sort.set(a)), Sort.set(a))
    val inter = Fun("set.inter", List(a), formals(Sort.set(a), Sort.set(a)), Sort.set(a))
    val minus = Fun("set.minus", List(a), formals(Sort.set(a), Sort.set(a)), Sort.set(a))
    val member = Fun("set.member", List(a), formals(a, Sort.set(a)), bool)
    val subset = Fun("set.subset", List(a), formals(Sort.set(a), Sort.set(a)), bool)
    val card = Fun("set.card", List(a), formals(Sort.set(a)), Sort.int)

    // not part of cvc5: proper subsets s < t
    val proper = Fun("set.proper_subset", List(a), formals(Sort.set(a), Sort.set(a)), bool)

    val all = List(empty, singleton, update, union, inter, minus, member, subset, card, proper)

  // finite multisets (bags) as in cvc5, where bag(x, n) holds x with multiplicity n,
  // the union adds multiplicities, the intersection takes the minimum, and the difference subtracts them
  object bag:
    val empty = Fun("bag.empty", List(a), Nil, Sort.bag(a))
    val make = Fun("bag", List(a), formals(a, Sort.int), Sort.bag(a))
    val union = Fun("bag.union_disjoint", List(a), formals(Sort.bag(a), Sort.bag(a)), Sort.bag(a))
    val inter = Fun("bag.inter_min", List(a), formals(Sort.bag(a), Sort.bag(a)), Sort.bag(a))
    val minus = Fun("bag.difference_subtract", List(a), formals(Sort.bag(a), Sort.bag(a)), Sort.bag(a))
    val count = Fun("bag.count", List(a), formals(a, Sort.bag(a)), Sort.int)
    val subbag = Fun("bag.subbag", List(a), formals(Sort.bag(a), Sort.bag(a)), bool)
    val card = Fun("bag.card", List(a), formals(Sort.bag(a)), Sort.int)
    val member = Fun("bag.member", List(a), formals(a, Sort.bag(a)), bool)

    // not part of cvc5: the multiplicity s[x] of an element, i.e., bag.count with the arguments swapped,
    // and proper submultisets s < t
    val select = Fun("bag.select", List(a), formals(Sort.bag(a), a), Sort.int)
    val proper = Fun("bag.proper_subbag", List(a), formals(Sort.bag(a), Sort.bag(a)), bool)

    val all = List(empty, make, union, inter, minus, count, subbag, card, member, select, proper)

  // finite maps, named like the sets of cvc5, which however has no such theory, where map.empty needs its type,
  // map.get is unspecified outside of the keys, map.update(m, n) overwrites m by n, and map.minus removes keys
  object map:
    val empty = Fun("map.empty", List(a, b), Nil, Sort.map(a, b))
    val singleton = Fun("map.singleton", List(a, b), formals(a, b), Sort.map(a, b))
    val card = Fun("map.card", List(a, b), formals(Sort.map(a, b)), Sort.int)
    val member = Fun("map.member", List(a, b), formals(a, Sort.map(a, b)), bool)
    val keys = Fun("map.keys", List(a, b), formals(Sort.map(a, b)), Sort.set(a))
    val values = Fun("map.values", List(a, b), formals(Sort.map(a, b)), Sort.set(b))
    val subset = Fun("map.subset", List(a, b), formals(Sort.map(a, b), Sort.map(a, b)), bool)
    val get = Fun("map.get", List(a, b), formals(Sort.map(a, b), a), b)
    val update = Fun("map.update", List(a, b), formals(Sort.map(a, b), Sort.map(a, b)), Sort.map(a, b))
    val minus = Fun("map.minus", List(a, b), formals(Sort.map(a, b), Sort.set(a)), Sort.map(a, b))
    // the update m[k := v] of a single key
    val store = Fun("map.store", List(a, b), formals(Sort.map(a, b), a, b), Sort.map(a, b))

    val all = List(empty, singleton, card, member, keys, values, subset, get, update, minus, store)

  object trace:
    val counter = Fun("counter", Nil, formals(Sort.int, Sort.int, Sort.int), Sort.trace(Sort.int))
    val current = Fun("current", List(a), formals(Sort.trace(a)), a)
    val butlast = Fun("butlast", List(a), formals(Sort.trace(a)), Sort.list(a))
    val earlier = Fun("earlier", List(a), formals(Sort.int, Sort.list(a)), a)

    val all = List(counter, current, butlast, earlier)

    val unspecified = Fun("unspecified", List(a), Nil, a)

    val stop = Fun("stop", List(a), formals(a), Sort.trace(a))
    val step = Fun("step", List(a), formals(a, Sort.trace(a)), Sort.trace(a))

  object list:
    val nil = Fun("nil", List(a), Nil, Sort.list(a))
    val cons = Fun("cons", List(a), formals(a, Sort.list(a)), Sort.list(a))

  val not = Fun("not", Nil, formals(bool), bool)
  val imp = Fun("=>", Nil, formals(bool, bool), bool)
  // equivalence, which SMT-LIB writes as = on Bool, declared by the preludes of all frontends
  val eqv = Fun("<=>", Nil, formals(bool, bool), bool)
  val and = Fun("and", Nil, formals(bool, bool), bool)
  val or = Fun("or", Nil, formals(bool, bool), bool)

  object int:
    val uminus = Fun("-", Nil, formals(Sort.int), Sort.int)
    val plus = Fun("+", Nil, formals(Sort.int, Sort.int), Sort.int)
    val minus = Fun("-", Nil, formals(Sort.int, Sort.int), Sort.int)
    val times = Fun("*", Nil, formals(Sort.int, Sort.int), Sort.int)
    val div = Fun("div", Nil, formals(Sort.int, Sort.int), Sort.int)
    val mod = Fun("mod", Nil, formals(Sort.int, Sort.int), Sort.int)

    val lt = Fun("<", Nil, formals(Sort.int, Sort.int), bool)
    val le = Fun("<=", Nil, formals(Sort.int, Sort.int), bool)
    val gt = Fun(">", Nil, formals(Sort.int, Sort.int), bool)
    val ge = Fun(">=", Nil, formals(Sort.int, Sort.int), bool)

    val all = List(uminus, plus, minus, times, div, mod, lt, le, gt, ge)

  object real:
    val uminus = Fun("-", Nil, formals(Sort.real), Sort.real)
    val plus = Fun("+", Nil, formals(Sort.real, Sort.real), Sort.real)
    val minus = Fun("-", Nil, formals(Sort.real, Sort.real), Sort.real)
    val times = Fun("*", Nil, formals(Sort.real, Sort.real), Sort.real)
    val div = Fun("/", Nil, formals(Sort.real, Sort.real), Sort.real)

    val lt = Fun("<", Nil, formals(Sort.real, Sort.real), bool)
    val le = Fun("<=", Nil, formals(Sort.real, Sort.real), bool)
    val gt = Fun(">", Nil, formals(Sort.real, Sort.real), bool)
    val ge = Fun(">=", Nil, formals(Sort.real, Sort.real), bool)

    val all = List(uminus, plus, minus, times, div, lt, le, gt, ge)
