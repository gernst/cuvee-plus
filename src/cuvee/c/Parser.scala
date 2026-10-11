package cuvee.c

import scala.collection.mutable

import cuvee.Error
import cuvee.core
import cuvee.core.State
import cuvee.core.Attrs

// resolution of a C translation unit into core procedures:
// integer types are Int (unbounded), _Bool is Bool, arrays are values of type Array Int T;
// functions are procedures whose result is the output `result`,
// and whose global variables modified, directly or by calls, are inferred;
// calls inside expressions are evaluated before the statement that contains them, in order
// `arch` is the data model, 32 or 64 bit Linux (ILP32 or LP64), see Config.arch;
// `unbounded` drops the ranges of the types of nondeterministic values, see Config.unbounded
class Parser(var state: State, arch: Int, unbounded: Boolean):
  // the signatures of the functions by name
  val functions = mutable.Map[String, Function]()

  // the global variables with their C types
  val globals = mutable.Map[String, (core.Var, Type)]()

  // the declared variables that sizeof may measure: the size of their elements in bytes, the sizes of their arrays,
  // and their initializers (see bytes)
  val declared = mutable.Map[core.Var, (BigInt, List[Option[Expr]], Option[Expr])]()

  // the local pointers that are never read, e.g. char *s; s = in; for an array in, whose assignments are dropped,
  // since other pointers than allocations are no arrays
  val unread = mutable.Set[core.Var]()

  // the context of a function body: its result, the temporary variables for the results of calls,
  // the statements of its labels, which a goto may resolve in its place, and the labels at its end
  case class Ctx(result: Option[(core.Var, Type)], temps: mutable.ListBuffer[core.Var],
                 labels: Map[String, Stmt] = Map(), ends: Set[String] = Set())

  type Scope = Map[String, (core.Var, Type)]

  def typ(t: Type): core.Type =
    t match
      case IntType(_, _) => state.types.sort("Int")
      case BoolType     => state.types.sort("Bool")
      case ArrayType(e) => state.types.sort("Array", List(state.types.sort("Int"), typ(e)))
      case VoidType     => Error.raise("void is not a type of values")
      case FloatType    => Error.raise("floating point numbers are not supported", t)

      // pointers are values of the background theory of C (resources/cuvee/c/prelude.bpl), which cannot be dereferenced,
      // where void * points to Void
      case PointerType(VoidType) => state.types.sort("Ptr", List(state.types.sort("Void")))
      case PointerType(e)        => state.types.sort("Ptr", List(typ(e)))

  // the null pointer constants of C, 0 and casts of it to pointer types, e.g. (void *) 0 for NULL
  def isNull(e: Expr): Boolean =
    e match
      case Num(text)               => literal(text) == 0
      case Cond(e, None)           => isNull(e)
      case Cast(PointerType(_), e) => isNull(e)
      case _                       => false

  // the value of global variables without initializer, where arrays are constant
  // the type of a declared variable with the sizes of its dimensions, e.g. int a[2][3]
  def array(t: Type, sizes: List[Option[Expr]]): Type =
    sizes.foldLeft(t)((elem, _) => ArrayType(elem))

  // pointers to memory for elements of type t, e.g. int *a = malloc(sizeof(int) * n), are arrays,
  // whose elements are arbitrary, or zero for calloc; the size is not used, as arrays are unbounded;
  // other pointers are values of type Ptr
  def allocation(x: String, t: Type, sizes: List[Option[Expr]], init: Option[Expr]): (Type, Option[Expr]) =
    def strip(e: Expr): Expr =
      e match
        case Cond(e, None)           => strip(e)
        case Cast(PointerType(_), e) => strip(e)
        case _                       => e

    def elements(size: Expr) =
      strip(size) match
        case App("*", List(SizeofType(_), _) | List(_, SizeofType(_))) => true
        case _                                                          => false

    init.map(strip) match
      case Some(Call("malloc" | "alloca", List(size))) if sizes.isEmpty && elements(size) =>
        (ArrayType(t), None)

      case Some(Call("calloc", List(_, size))) if sizes.isEmpty && strip(size).isInstanceOf[SizeofType] =>
        (ArrayType(t), Some(Items(Nil)))

      // other pointers are values, e.g. int *p = NULL, which cannot be dereferenced
      case _ =>
        Error.report("arrays of pointers are not supported", x):
          require(sizes.isEmpty)
        (PointerType(t), init)

  def zero(t: Type): core.Expr =
    t match
      case IntType(_, _) => state.exprs.num(0)
      case BoolType     => state.exprs.const("false")
      case ArrayType(e) => state.exprs.app("const", List(zero(e)))
      case PointerType(_) => state.exprs.const("null")
      case VoidType     => Error.raise("void is not a type of values")
      case FloatType    => Error.raise("floating point numbers are not supported", t)

  def temp(ctx: Ctx, t: Type): core.Var =
    val x = state.exprs.formal("tmp", typ(t)).fresh
    ctx.temps += x
    x

  // conversions between integers and truth values as in C
  def toInt(expr: core.Expr, t: Type): core.Expr =
    t match
      case IntType(_, _) => expr
      case BoolType => state.exprs.app("number", List(expr))
      case _        => Error.raise("not an integer", expr)

  def toBool(expr: core.Expr, t: Type): core.Expr =
    t match
      case BoolType => expr
      case IntType(_, _) => state.exprs.app("truth", List(expr))
      case PointerType(_) => state.exprs.app("not", List(state.exprs.app("=", List(expr, state.exprs.const("null")))))
      case _        => Error.raise("not a truth value", expr)

  // the size of an integer type in bytes, where long has 4 bytes in the data model ILP32 and 8 bytes in LP64
  def size(t: IntType): Int =
    t.rank match
      case "char"  => 1
      case "short" => 2
      case "int"   => 4
      case "long"  => arch / 8
      case _       => 8

  // the least and the greatest value of an integer type
  def range(t: IntType): (BigInt, BigInt) =
    val bits = 8 * size(t)
    if t.signed
    then (-BigInt(2).pow(bits - 1), BigInt(2).pow(bits - 1) - 1)
    else (BigInt(0), BigInt(2).pow(bits) - 1)

  // the function of the prelude that computes modulo the range of an unsigned type, by its size, e.g. uint for
  // unsigned int, and for unsigned long in ILP32; none for signed types, whose overflow is undefined, and with
  // -unbounded, where unsigned integers are unbounded as well
  def overflow(t: Type): Option[String] =
    t match
      case t: IntType if !t.signed && !unbounded =>
        size(t) match
          case 1 => Some("uchar")
          case 2 => Some("ushort")
          case 4 => Some("uint")
          case _ => Some("ulonglong")
      case _ => None

  // the integer promotions of C: types of lower rank than int, whose values int contains, and _Bool are int
  def promote(t: Type): IntType =
    t match
      case t: IntType if size(t) >= 4 => t
      case _                          => IntType.int

  def rank(t: IntType): Int =
    IntType.ranks.indexOf(t.rank)

  // the usual arithmetic conversions of C: the common type of the operands of a binary operator, e.g. unsigned int
  // for int and unsigned int, which converts the signed operand
  def common(lt: Type, rt: Type): IntType =
    val (a, b) = (promote(lt), promote(rt))
    if a.signed == b.signed
    then if rank(a) >= rank(b) then a else b
    else
      val (u, s) = if a.signed then (b, a) else (a, b)
      if rank(u) >= rank(s) then u
      else if size(s) > size(u) then s
      else IntType(false, s.rank)

  // whether the values of type `from` need no conversion to type `to`: all but those to an unsigned type, unless they
  // are truth values or of an unsigned type that is not larger, as integers are unbounded
  def fits(from: Type, to: Type): Boolean =
    from match
      case _ if overflow(to).isEmpty => true
      case BoolType                  => true
      case from: IntType             => !from.signed && size(from) <= size(to.asInstanceOf[IntType])
      case _                         => false

  // a value of type `from` converted to type `to`, which is modulo the range of an unsigned type, unless it is within
  // it already: a constant in it or a value of a type that fits (see fits)
  def convert(e: core.Expr, from: Type, to: Type): core.Expr =
    (overflow(to), to, e) match
      case (Some(f), to: IntType, core.Lit(n: BigInt, _)) if range(to)._1 <= n && n <= range(to)._2 => e
      case (Some(f), _, _) if !fits(from, to)                                                    => state.exprs.app(f, List(e))
      case _                                                                                     => e

  // the result of an arithmetic operator in the integer type `t`, which wraps around for unsigned types after
  // additions, subtractions, multiplications, and shifts left; quotients, remainders, and shifts right of values
  // within the range stay within it, and the bit operations are declared only
  def wrap(op: String, e: core.Expr, t: IntType): core.Expr =
    (op, overflow(t)) match
      case ("+" | "-" | "*" | "<<", Some(f)) => state.exprs.app(f, List(e))
      case _                                 => e

  // a binary arithmetic operator applied to the operands converted to their common type, which is the type of the
  // result, where shifts have the promoted type of their left operand, whose right operand is not converted
  def binary(op: String, left: core.Expr, lt: Type, right: core.Expr, rt: Type): (core.Expr, IntType) =
    val shift = op == "<<" || op == ">>"
    val t = if shift then promote(lt) else common(lt, rt)
    val left_ = convert(toInt(left, lt), lt, t)
    val right_ = if shift then toInt(right, rt) else convert(toInt(right, rt), rt, t)
    (wrap(op, arith(op, left_, right_), t), t)

  def arith(op: String, a: core.Expr, b: core.Expr): core.Expr =
    op match
      case "+" => state.exprs.app("+", List(a, b))
      case "-" => state.exprs.app("-", List(a, b))
      case "*" => state.exprs.app("*", List(a, b))
      // division and remainder truncate towards zero in C (see resources/cuvee/c/prelude.bpl)
      case "/" => state.exprs.app("quot", List(a, b))
      case "%" => state.exprs.app("rem", List(a, b))
      // shifts by constants are multiplications and divisions by powers of 2 of the unbounded integers,
      // where the division rounds down, like the arithmetic shift of negative numbers;
      // other shifts and the bit operations are declared functions (see resources/cuvee/c/prelude.bpl)
      case "<<" | ">>" =>
        b match
          case core.Lit(n: BigInt, _) if 0 <= n && n < 64 =>
            val power = state.exprs.num(BigInt(2).pow(n.toInt))
            if op == "<<" then state.exprs.app("*", List(a, power)) else state.exprs.app("div", List(a, power))
          case _ =>
            state.exprs.app(if op == "<<" then "shl" else "shr", List(a, b))
      case "&" => state.exprs.app("bitand", List(a, b))
      case "|" => state.exprs.app("bitor", List(a, b))
      case "^" => state.exprs.app("bitxor", List(a, b))
      case _   => Error.raise("unknown arithmetic operator", op)

  // an expression together with the statements that evaluate the calls in it first, and its C type
  // the value of an integer constant, decimal, octal (0...), or hexadecimal (0x...),
  // whose suffixes u and l are dropped, as integers are unbounded, or of a character constant, its code
  def literal(text: String): BigInt =
    if text.startsWith("'")
    then character(text.drop(1).dropRight(1))
    else
      val digits = text.toLowerCase.stripSuffix("u").stripSuffix("l").stripSuffix("l").stripSuffix("u")
      if digits.startsWith("0x") then BigInt(digits.drop(2), 16)
      else if digits.length > 1 && digits.startsWith("0") then BigInt(digits.drop(1), 8)
      else BigInt(digits)

  // the type of an integer constant: the first of int, long, and long long, from long with the suffix l and from long
  // long with ll, whose range contains its value, unsigned with the suffix u, where octal and hexadecimal constants
  // may also be of the unsigned version of each; character constants are int
  def literalType(text: String): IntType =
    if text.startsWith("'")
    then IntType.int
    else
      val lower = text.toLowerCase
      val value = literal(text)
      val unsigned = lower.contains('u')
      val decimal = !lower.startsWith("0") || lower == "0" || lower.startsWith("0u") || lower.startsWith("0l")
      val ranks = IntType.ranks.drop(2 + lower.count(_ == 'l').min(2))
      val candidates =
        for
          rank <- ranks
          signed <- if unsigned then List(false) else if decimal then List(true) else List(true, false)
        yield IntType(signed, rank)
      candidates.find(t => range(t)._1 <= value && value <= range(t)._2).getOrElse(IntType(false, "longlong"))

  // the size of an integer type in bytes, where long has 4 bytes in the data model ILP32 and 8 bytes in LP64
  def sizeof(words: List[String]): BigInt =
    val longs = words.count(_ == "long")
    if words.contains("char") || words.contains("_Bool") || words.contains("bool") then 1
    else if words.contains("short") then 2
    else if longs == 0 then 4
    else if longs == 1 then arch / 8
    else 8

  // the size in bytes of the elements of a declared variable, by the words of its integer type
  def elem(t: Type, words: List[String]): BigInt =
    t match
      case IntType(_, _) => sizeof(words)
      case BoolType => 1
      case _        => arch / 8

  // the size in bytes of an expression, sizeof e, e.g. sizeof(a) / sizeof(a[0]), by the declared types of variables
  // and the sizes of their arrays, otherwise by its type, where pointers and arrays that are parameters are addresses;
  // `e` is not evaluated
  def bytes(scope: Scope, ctx: Ctx, e: Expr): BigInt =
    shape(scope, e) match
      case Some((size, dims)) =>
        size * dims.product

      case None =>
        val (_, _, t) = expr(scope, ctx, e)
        t match
          case BoolType => 1
          case t: IntType => size(t)
          case _        => arch / 8

  // the size of the elements and the sizes of the dimensions of an array variable, or of an element of it,
  // where an array without size has the number of items of its initializer
  def shape(scope: Scope, e: Expr): Option[(BigInt, List[BigInt])] =
    e match
      case Id(x) if scope.contains(x) && declared.contains(scope(x)._1) =>
        val (size, sizes, init) = declared(scope(x)._1)
        val dims =
          for (n, i) <- sizes.zipWithIndex
          yield (n, init) match
            case (Some(n), _)                         => constant(n)
            case (None, Some(Items(items))) if i == 0 => BigInt(items.length)
            case _                                    => Error.raise("sizeof of an array without size", x)
        Some((size, dims))

      case Index(base, _) =>
        shape(scope, base).collect:
          case (size, _ :: dims) => (size, dims)

      case Cond(e, None) =>
        shape(scope, e)

      case _ =>
        None

  // the value of a constant expression, e.g. the size of an array 1024 * 100
  def constant(e: Expr): BigInt =
    e match
      case Num(text)             => literal(text)
      case SizeofType(words)     => sizeof(words)
      case Cond(e, None)         => constant(e)
      case App("-", List(a))     => -constant(a)
      case App("+", List(a, b))  => constant(a) + constant(b)
      case App("-", List(a, b))  => constant(a) - constant(b)
      case App("*", List(a, b))  => constant(a) * constant(b)
      case App("/", List(a, b))  => constant(a) / constant(b)
      case App("%", List(a, b))  => constant(a) % constant(b)
      case App("<<", List(a, b)) => constant(a) << constant(b).toInt
      case _                     => Error.raise("size of an array that is not constant", e)

  // the simple escape sequences of C
  val escapes = Map('a' -> 7, 'b' -> 8, 't' -> 9, 'n' -> 10, 'v' -> 11, 'f' -> 12, 'r' -> 13, '\\' -> 92, '\'' -> 39, '"' -> 34, '?' -> 63)

  def character(body: String): BigInt =
    body match
      case s"\\x$hex"                         => BigInt(hex, 16)
      case s"\\$oct" if oct.forall(_.isDigit) => BigInt(oct, 8)
      case s"\\$c" if c.length == 1 && escapes.contains(c.head) => BigInt(escapes(c.head))
      case _ if body.length == 1                => BigInt(body.head.toInt)
      case _                                  => Error.raise("unsupported character constant", body)

  def expr(scope: Scope, ctx: Ctx, e: Expr): (List[core.Prog], core.Expr, Type) =
    e match
      case Num(text) =>
        (Nil, state.exprs.num(literal(text)), literalType(text))

      case FloatNum(_) =>
        Error.raise("floating point numbers are not supported", e)

      case Id("true") if !scope.contains("true") =>
        (Nil, state.exprs.const("true"), BoolType)

      case Id("false") if !scope.contains("false") =>
        (Nil, state.exprs.const("false"), BoolType)

      case Id(x) =>
        Error.report("unknown variable", x):
          require(scope.contains(x))
        val (v, t) = scope(x)
        (Nil, v, t)

      case Index(base, index) =>
        val (pre1, base_, t) = expr(scope, ctx, base)
        val (pre2, index_) = int(scope, ctx, index)
        t match
          case ArrayType(elem) => (pre1 ++ pre2, state.exprs.app("select", List(base_, index_)), elem)
          case _               => Error.raise("indexing of an expression that is not an array", base)

      case Call(f, Nil) if f.startsWith("__VERIFIER_nondet_") =>
        val t = if f == "__VERIFIER_nondet_bool" then BoolType else integer(f.stripPrefix("__VERIFIER_nondet_")).getOrElse(IntType.int)
        val x = temp(ctx, t)
        (List(havoc(f, x)), x, t)

      case Call(f, args) =>
        val (pre, args_) = arguments(scope, ctx, f, args)
        val ret = functions(f).typ

        Error.report("call of a void function inside an expression", f):
          require(ret != VoidType)

        val x = temp(ctx, ret)
        (pre :+ state.progs.call(f, args_, List(x)), x, ret)

      case App("-", List(arg)) =>
        val (pre, arg_, t) = expr(scope, ctx, arg)
        val t_ = promote(t)
        (pre, wrap("-", state.exprs.app("-", List(toInt(arg_, t))), t_), t_)

      case App("!", List(arg)) =>
        val (pre, arg_) = cond(scope, ctx, arg)
        (pre, state.exprs.app("not", List(arg_)), BoolType)

      case App("~", List(arg)) =>
        val (pre, arg_, t) = expr(scope, ctx, arg)
        (pre, state.exprs.app("bitnot", List(toInt(arg_, t))), promote(t))

      case App("&", List(_)) =>
        Error.raise("the address of a variable is not supported", e)

      case App("*", List(_)) =>
        Error.raise("the dereference of a pointer is not supported", e)

      case App(op @ ("&&" | "||"), List(left, right)) =>
        val (pre1, left_) = cond(scope, ctx, left)
        val (pre2, right_) = cond(scope, ctx, right)

        if pre2.isEmpty
        then
          val phi = if op == "&&" then state.exprs.app("and", List(left_, right_)) else state.exprs.app("or", List(left_, right_))
          (pre1, phi, BoolType)
        else
          // the calls of the right operand are made only if the left one does not determine the result
          val x = temp(ctx, BoolType)
          val right__ = state.progs.block(Nil, pre2 :+ state.progs.assign(List(x), List(right_)))
          val prog =
            if op == "&&"
            then state.progs.if_(left_, right__, state.progs.assign(List(x), List(state.exprs.const("false"))))
            else state.progs.if_(left_, state.progs.assign(List(x), List(state.exprs.const("true"))), right__)
          (pre1 :+ prog, x, BoolType)

      // a pointer compared with a null pointer constant, which has the type of the pointer
      case App(op @ ("==" | "!="), List(left, right)) if isNull(right) && !isNull(left) || isNull(left) && !isNull(right) =>
        val (nonnull, _) = if isNull(right) then (left, right) else (right, left)
        val (pre, e_, t) = expr(scope, ctx, nonnull)
        val eq =
          t match
            case PointerType(_) => state.exprs.app("=", List(e_, state.exprs.const("null")))
            case _              => state.exprs.app("=", List(toInt(e_, t), state.exprs.num(0)))
        (pre, if op == "==" then eq else state.exprs.app("not", List(eq)), BoolType)

      case App(op @ ("==" | "!="), List(left, right)) =>
        val (pre1, left_, lt) = expr(scope, ctx, left)
        val (pre2, right_, rt) = expr(scope, ctx, right)

        val eq = (lt, rt) match
          case (BoolType, BoolType)                 => state.exprs.app("=", List(left_, right_))
          case (ArrayType(_), _) | (_, ArrayType(_)) => state.exprs.app("=", List(left_, right_))
          case (PointerType(_), _) | (_, PointerType(_)) =>
            // e.g. int * and long *, which are both pointers to integers
            Error.report("comparison of pointers of different types", left, right):
              require(typ(lt) == typ(rt))
            state.exprs.app("=", List(left_, right_))
          case _ =>
            val t = common(lt, rt)
            state.exprs.app("=", List(convert(toInt(left_, lt), lt, t), convert(toInt(right_, rt), rt, t)))

        (pre1 ++ pre2, if op == "==" then eq else state.exprs.app("not", List(eq)), BoolType)

      // in the common type of the operands, e.g. -1 < 1u is false, as -1 is converted to unsigned int
      case App(op @ ("<" | "<=" | ">" | ">="), List(left, right)) =>
        val (pre1, left0, lt) = expr(scope, ctx, left)
        val (pre2, right0, rt) = expr(scope, ctx, right)
        val t = common(lt, rt)
        val left_ = convert(toInt(left0, lt), lt, t)
        val right_ = convert(toInt(right0, rt), rt, t)

        val phi = op match
          case "<"  => state.exprs.app("<", List(left_, right_))
          case "<=" => state.exprs.app("<=", List(left_, right_))
          case ">"  => state.exprs.app(">", List(left_, right_))
          case _    => state.exprs.app(">=", List(left_, right_))

        (pre1 ++ pre2, phi, BoolType)

      case App(op, List(left, right)) =>
        val (pre1, left_, lt) = expr(scope, ctx, left)
        val (pre2, right_, rt) = expr(scope, ctx, right)
        val (e_, t) = binary(op, left_, lt, right_, rt)
        (pre1 ++ pre2, e_, t)

      case Cond(e, None) =>
        expr(scope, ctx, e)

      // casts to signed integer types are the identity, as integers are unbounded, those to unsigned types wrap around
      case Cast(t: IntType, e) =>
        val (pre, e_, t_) = expr(scope, ctx, e)
        (pre, convert(toInt(e_, t_), t_, t), t)

      case Cast(BoolType, e) =>
        val (pre, e_) = cond(scope, ctx, e)
        (pre, e_, BoolType)

      case Cast(t @ PointerType(_), e) if isNull(e) =>
        (Nil, state.exprs.const("null"), t)

      case Cast(t @ PointerType(_), e) =>
        val (pre, e_, t_) = expr(scope, ctx, e)
        Error.report("unsupported cast", t, e):
          require(t == t_)
        (pre, e_, t)

      case Cast(t, e) =>
        Error.raise("unsupported cast", t, e)

      case Items(_) =>
        Error.raise("initializer list outside of a declaration", e)

      // the update is made before the expression, whose value is the old one for x++ and the new one for ++x
      case Incr(lhs, op, post) =>
        val t = lvalue(scope, lhs)
        val (pre, now, _) = expr(scope, ctx, lhs)
        val update = assign(scope, ctx, lhs, compound(op), Num("1"))

        if post
        then
          val old = temp(ctx, t)
          (pre ++ (state.progs.assign(List(old), List(now)) :: update), old, t)
        else (pre ++ update, now, t)

      // of type size_t, unsigned long
      case SizeofType(words) =>
        (Nil, state.exprs.num(sizeof(words)), IntType(false, "long"))

      case SizeofExpr(arg) =>
        (Nil, state.exprs.num(bytes(scope, ctx, arg)), IntType(false, "long"))

      case Cond(test, Some((left, right))) =>
        val (pre0, test_) = cond(scope, ctx, test)
        val (pre1, left_, lt) = expr(scope, ctx, left)
        val (pre2, right_, rt) = expr(scope, ctx, right)

        val (t, left__, right__) =
          if lt == BoolType && rt == BoolType
          then (BoolType, left_, right_)
          else
            val t = common(lt, rt)
            (t, convert(toInt(left_, lt), lt, t), convert(toInt(right_, rt), rt, t))

        if pre1.isEmpty && pre2.isEmpty
        then (pre0, state.exprs.app("ite", List(test_, left__, right__)), t)
        else
          // the calls and updates of a branch are made only if it is taken
          val x = temp(ctx, t)
          val prog =
            state.progs.if_(
              test_,
              state.progs.block(Nil, pre1 :+ state.progs.assign(List(x), List(left__))),
              state.progs.block(Nil, pre2 :+ state.progs.assign(List(x), List(right__)))
            )
          (pre0 :+ prog, x, t)

      case App(op, args) =>
        Error.raise("unknown operator", op, args)

  def int(scope: Scope, ctx: Ctx, e: Expr): (List[core.Prog], core.Expr) =
    val (pre, e_, t) = expr(scope, ctx, e)
    (pre, toInt(e_, t))

  def cond(scope: Scope, ctx: Ctx, e: Expr): (List[core.Prog], core.Expr) =
    val (pre, e_, t) = expr(scope, ctx, e)
    (pre, toBool(e_, t))

  // a value of C type `t`, converted as in C
  def value(scope: Scope, ctx: Ctx, e: Expr, t: Type): (List[core.Prog], core.Expr) =
    t match
      case IntType(_, _) =>
        val (pre, e_, t_) = expr(scope, ctx, e)
        (pre, convert(toInt(e_, t_), t_, t))
      case BoolType => cond(scope, ctx, e)
      case PointerType(_) if isNull(e) => (Nil, state.exprs.const("null"))

      // the elements that are not given are zero, as in C
      case ArrayType(elem) if e.isInstanceOf[Items] =>
        val Items(items) = e: @unchecked
        val results = items.map(value(scope, ctx, _, elem))
        val array =
          results.zipWithIndex.foldLeft(zero(t)):
            case (array, ((_, item), i)) => state.exprs.app("store", List(array, state.exprs.num(BigInt(i)), item))
        (results.flatMap(_._1), array)

      case _ =>
        val (pre, e_, t_) = expr(scope, ctx, e)
        // e.g. arrays of int passed for arrays of unsigned int, which are both arrays of integers
        Error.report("type mismatch", e, t, t_):
          require(typ(t) == typ(t_))
        (pre, e_)

  // the arguments of a call to function `f`, converted to the types of its parameters
  def arguments(scope: Scope, ctx: Ctx, f: String, args: List[Expr]): (List[core.Prog], List[core.Expr]) =
    Error.report("unknown function", f):
      require(functions.contains(f))

    val params = functions(f).params
    Error.report("wrong number of arguments", f, args):
      require(params.length == args.length)

    val results =
      for ((t, _), arg) <- params zip args
      yield value(scope, ctx, arg, t)

    (results.flatMap(_._1), results.map(_._2))

  // pointer parameters that the body indexes but neither assigns nor writes through, e.g. int linear_search(int *a, ...),
  // are arrays, which are values, such that the caller passes its array; other pointers are values of type Ptr
  def readonly(f: Function): Function =
    f.body match
      case Some(body) =>
        val written = assigned(body)
        val read = indexed(body)
        val params =
          for (t, x) <- f.params
          yield t match
            case PointerType(e) if e != VoidType && read.contains(x) && !written.contains(x) => (ArrayType(e), x)
            case _                                                                            => (t, x)
        f.copy(params = params)

      case None =>
        f

  // the variables that are indexed in a statement, e.g. a in a[i]
  def indexed(s: Stmt): Set[String] =
    s match
      case Assign(lhs, _, rhs)           => indexed(lhs) ++ indexed(rhs)
      case ExprStmt(e)                   => indexed(e)
      case Return(e)                     => e.toSet.flatMap(indexed)
      case Decl(_, _, decls)             => decls.flatMap(_.init).toSet.flatMap(indexed)
      case If(test, left, right)         => indexed(test) ++ indexed(left) ++ right.toSet.flatMap(indexed)
      case While(test, body)             => indexed(test) ++ indexed(body)
      case DoWhile(body, test)           => indexed(test) ++ indexed(body)
      case For(init, test, step, body)   => init.toSet.flatMap(indexed) ++ test.toSet.flatMap(indexed) ++ step.toSet.flatMap(indexed) ++ indexed(body)
      case Block(stmts)                  => stmts.toSet.flatMap(indexed)
      case Labeled(_, stmt)              => indexed(stmt)
      case Switch(test, body)            => indexed(test) ++ body.toSet.flatMap(indexed)
      case Case(_, stmt)                 => indexed(stmt)
      case _                             => Set()

  // the variables that are read in a statement, all but those assigned by x = e, including the arrays of a[i] = e
  def reads(s: Stmt): Set[String] =
    s match
      case Assign(Id(_), "=", rhs)       => reads(rhs)
      case Assign(lhs, _, rhs)           => reads(lhs) ++ reads(rhs)
      case ExprStmt(e)                   => reads(e)
      case Return(e)                     => e.toSet.flatMap(reads)
      case Decl(_, _, decls)             => decls.flatMap(_.init).toSet.flatMap(reads)
      case If(test, left, right)         => reads(test) ++ reads(left) ++ right.toSet.flatMap(reads)
      case While(test, body)             => reads(test) ++ reads(body)
      case DoWhile(body, test)           => reads(test) ++ reads(body)
      case For(init, test, step, body)   => init.toSet.flatMap(reads) ++ test.toSet.flatMap(reads) ++ step.toSet.flatMap(reads) ++ reads(body)
      case Loop(test, body, step)        => test.toSet.flatMap(reads) ++ step.toSet.flatMap(reads) ++ reads(body)
      case Block(stmts)                  => stmts.toSet.flatMap(reads)
      case Labeled(_, stmt)              => reads(stmt)
      case Switch(test, body)            => reads(test) ++ body.toSet.flatMap(reads)
      case Case(value, stmt)             => value.toSet.flatMap(reads) ++ reads(stmt)
      case _                             => Set()

  def reads(e: Expr): Set[String] =
    e match
      case Id(x) => Set(x)
      case _     => parts(e).toSet.flatMap(reads)

  def indexed(e: Expr): Set[String] =
    e match
      case Index(Id(x), index) => indexed(index) + x
      case _                   => parts(e).toSet.flatMap(indexed)

  // the statements of a block, whose declarations are the local variables of the core block,
  // which are renamed if they shadow variables in scope
  // `body` for the body of a function, where a local variable result of the type of its result without initializer,
  // as the printer declares it (see c.Printer), is the result itself
  def block(scope: Scope, ctx: Ctx, stmts: List[Stmt], body: Boolean = false): core.Prog =
    val locals = mutable.ListBuffer[core.Var]()
    var scope_ = scope

    val progs =
      for stmt <- stmts
      yield stmt match
        case Decl(t, words, decls) =>
          for
            Declarator(pointer, x, sizes, init_) <- decls
            prog <-
              val (t_, init) = if pointer then allocation(x, t, sizes, init_) else (array(t, sizes), init_)
              val v = state.exprs.formal(x, typ(t_))
              val result = body && init.isEmpty && ctx.result.exists((r, t) => r == v && t == t_)
              // also apart from the result otherwise, e.g. a local variable result of a block, which return e assigns to
              // the result
              val v_ = if !result && (scope_.values.exists(_._1.name == v.name) || ctx.result.exists(_._1.name == v.name)) then v.fresh else v
              if !pointer then declared(v_) = (elem(t, words), sizes, init_)
              if pointer && t_.isInstanceOf[PointerType] && !stmts.exists(reads(_).contains(x)) then unread += v_
              if !result then locals += v_
              scope_ = scope_ + (x -> (v_, t_))
              init.toList.flatMap(assign(scope_, ctx, Id(x), "=", _))
          yield prog

        case _ =>
          this.stmt(scope_, ctx, stmt)

    state.progs.block(locals.toList, progs.flatten)

  def wrap(progs: List[core.Prog]): core.Prog =
    progs match
      case List(prog) => prog
      case _          => state.progs.block(Nil, progs)

  def stmt(scope: Scope, ctx: Ctx, s: Stmt): List[core.Prog] =
    s match
      case Empty =>
        Nil

      case Break =>
        List(state.progs.break)

      case Continue =>
        List(state.progs.continue)

      case _: Decl =>
        List(block(scope, ctx, List(s)))

      case Block(stmts) =>
        List(block(scope, ctx, stmts))

      case Labeled(_, stmt) =>
        this.stmt(scope, ctx, stmt)

      case Goto(label) =>
        goto(scope, ctx, label, Set())

      case Switch(test, body) =>
        stmt(scope, ctx, switch_(test, body))

      case Case(_, _) =>
        Error.raise("case outside of a switch", s)

      // expressions without ?: (see Grammar.expr), which are matched against calls below
      case ExprStmt(Cond(e, None)) =>
        stmt(scope, ctx, ExprStmt(e))

      case Assign(lhs, op, Cond(rhs, None)) =>
        stmt(scope, ctx, Assign(lhs, op, rhs))

      case Assign(lhs, op, rhs) =>
        assign(scope, ctx, lhs, compound.getOrElse(op, op), rhs)

      // __VERIFIER_assert is defined in the harness of SV-COMP by a call of reach_error
      case ExprStmt(Call("assert" | "__VERIFIER_assert", List(phi))) =>
        val (pre, phi_) = cond(scope, ctx, phi)
        pre :+ state.progs.assert(phi_)

      case ExprStmt(Call("__VERIFIER_assume", List(phi))) =>
        val (pre, phi_) = cond(scope, ctx, phi)
        pre :+ state.progs.assume(phi_)

      case ExprStmt(Call("reach_error" | "__VERIFIER_error", Nil)) =>
        List(state.progs.assert(state.exprs.const("false")))

      // allocations are arrays, which are values
      case ExprStmt(Call("free", List(_))) =>
        Nil

      case ExprStmt(Call("abort", Nil)) =>
        List(state.progs.assume(state.exprs.const("false")))

      // calls as statements, whose result is discarded
      case ExprStmt(Call(f, args)) if functions.contains(f) =>
        val (pre, args_) = arguments(scope, ctx, f, args)
        val ret = functions(f).typ
        val res = if ret == VoidType then Nil else List(temp(ctx, ret))
        pre :+ state.progs.call(f, args_, res)

      case ExprStmt(e) =>
        val (pre, _, _) = expr(scope, ctx, e)
        pre

      case If(test, left, right) =>
        val (pre, test_) = cond(scope, ctx, test)
        val left_ = wrap(stmt(scope, ctx, left))
        val right_ = wrap(right.toList.flatMap(stmt(scope, ctx, _)))
        pre :+ state.progs.if_(test_, left_, right_)

      case While(test, body) =>
        val (test_, check) = guard(scope, ctx, test)
        List(while_(test_, wrap(check ++ stmt(scope, ctx, body))))

      // the test is evaluated after each iteration, also after continue, but not before the first one
      case DoWhile(body, test) =>
        val (test_, check) = guard(scope, ctx, test)
        val first = temp(ctx, BoolType)

        val body_ =
          if check.isEmpty
          then state.progs.block(Nil, state.progs.assign(List(first), List(state.exprs.const("false"))) :: stmt(scope, ctx, body))
          else state.progs.block(Nil, state.progs.if_(state.exprs.app("not", List(first)), state.progs.block(Nil, check), skip) :: state.progs.assign(List(first), List(state.exprs.const("false"))) :: stmt(scope, ctx, body))

        List(state.progs.assign(List(first), List(state.exprs.const("true"))), while_(state.exprs.app("or", List(first, test_)), body_))

      // the initialization may declare variables, whose scope is the loop
      case For(init, test, step, body) =>
        List(block(scope, ctx, init.toList :+ Loop(test, body, step)))

      // continue must execute the step: the body is an inner loop that is left by break instead of continue,
      // and a break of the body sets a flag that leaves the outer loop
      case Loop(test, body, step) =>
        val (test_, check) = test.map(guard(scope, ctx, _)).getOrElse((state.exprs.const("true"), Nil))
        val body_ = stmt(scope, ctx, body)
        val step_ = step.toList.flatMap(stmt(scope, ctx, _))

        if !body_.exists(continues)
        then List(while_(test_, state.progs.block(Nil, check ++ body_ ++ step_)))
        else
          val brk = temp(ctx, BoolType)
          val inner = while_(state.exprs.const("true"), state.progs.block(Nil, body_.map(exits(brk, _)) :+ state.progs.break))
          val leave = state.progs.if_(brk, state.progs.break, skip)
          val outer = while_(test_, state.progs.block(Nil, check ++ List(inner, leave) ++ step_))
          List(state.progs.assign(List(brk), List(state.exprs.const("false"))), outer)

      case Return(None) =>
        Error.report("return without value from a function with result"):
          require(ctx.result.isEmpty)
        List(state.progs.return_)

      case Return(Some(e)) =>
        Error.report("return with value from a void function", e):
          require(ctx.result.isDefined)

        val Some((result, t)) = ctx.result: @unchecked
        val (pre, e_) = value(scope, ctx, e, t)
        // return result of the local variable that is the result itself (see block)
        if e_ == result
        then pre :+ state.progs.return_
        else pre ++ List(state.progs.assign(List(result), List(e_)), state.progs.return_)

  val skip = state.progs.skip

  // a goto whose label marks a statement that does not fall through, e.g. END: return 0; or
  // ERROR: { reach_error(); abort(); }, is that statement in its place, since control does not come back;
  // a label that marks a goto to itself, e.g. STUCK: goto STUCK;, is a loop without exit;
  // other gotos, e.g. those of state machines, are not supported
  def goto(scope: Scope, ctx: Ctx, label: String, visited: Set[String]): List[core.Prog] =
    Error.report("unknown label", label):
      require(ctx.labels.contains(label) || ctx.ends.contains(label))

    // the end of the function body, e.g. END: ; as its last statement
    if ctx.ends.contains(label)
    then List(state.progs.return_)
    else
      ctx.labels(label) match
        case Goto(next) if visited.contains(next) || next == label =>
          List(state.progs.assume(state.exprs.const("false")))

        case Goto(next) =>
          goto(scope, ctx, next, visited + label)

        case target if stops(target) =>
          stmt(scope, ctx, target)

        case _ =>
          Error.raise("goto to a label whose statement falls through is not supported", label)

  // whether a statement never falls through: a return, an abort, or a block that ends with such a statement,
  // without labels or gotos inside, whose targets would be resolved in the wrong place
  def stops(s: Stmt): Boolean =
    s match
      case Return(_)                                        => true
      case ExprStmt(Call("abort" | "exit", _))              => true
      case ExprStmt(Cond(e, None))                          => stops(ExprStmt(e))
      case Labeled(_, stmt)                                 => stops(stmt)
      case Block(stmts) if stmts.nonEmpty                   => stmts.forall(unlabeled) && stops(stmts.last)
      case _                                                => false

  // statements without labels and gotos
  def unlabeled(s: Stmt): Boolean =
    s match
      case Labeled(_, _) | Goto(_)       => false
      case Block(stmts)                  => stmts.forall(unlabeled)
      case If(_, left, right)            => unlabeled(left) && right.forall(unlabeled)
      case While(_, body)                => unlabeled(body)
      case DoWhile(body, _)              => unlabeled(body)
      case For(_, _, _, body)            => unlabeled(body)
      case Switch(_, body)               => body.forall(unlabeled)
      case Case(_, stmt)                 => unlabeled(stmt)
      case _                             => true

  // a switch is a chain of conditionals over the value of its test, which is evaluated once, where each case is
  // followed by the statements of the cases it falls through to, up to the first break, which are copied;
  // statements before the first case are unreachable; a break nested inside the statements of a case is not
  // supported, since the copies end at breaks between the statements only
  def switch_(test: Expr, body: List[Stmt]): Stmt =
    val groups = mutable.ListBuffer[(List[Option[Expr]], mutable.ListBuffer[Stmt])]()
    for s <- body
    do
      s match
        case Case(_, _) =>
          val (values, first) = cases(s)
          groups += ((values, mutable.ListBuffer(first)))
        case _ if groups.nonEmpty =>
          groups.last._2 += s
        case _ =>

    val cases_ = groups.toList.map((values, stmts) => (values, stmts.toList))

    def falls(i: Int): Stmt =
      val stmts = cases_.drop(i).flatMap(_._2).takeWhile(_ != Break)
      Error.report("break nested inside a case of a switch is not supported", test):
        require(!stmts.exists(breaks))
      Block(stmts)

    val x = "switch_" + switches.next()
    val default = cases_.indexWhere(_._1.contains(None))

    val chain =
      cases_.zipWithIndex.foldRight(if default >= 0 then Some(falls(default)) else None):
        case (((values, _), i), rest) =>
          val tests = values.flatten.map(c => App("==", List(Id(x), c)))
          if tests.isEmpty
          then rest
          else Some(If(tests.reduce((a, b) => App("||", List(a, b))), falls(i), rest))

    Block(Decl(IntType.int, List("int"), List(Declarator(false, x, Nil, Some(test)))) :: chain.toList)

  // the numbers of the variables of the tests of switches
  val switches = Iterator.from(1)

  // the values of the labels of a case, case 1: case 2: s, and its statement
  def cases(s: Stmt): (List[Option[Expr]], Stmt) =
    s match
      case Case(value, stmt) =>
        val (values, stmt_) = cases(stmt)
        (value :: values, stmt_)
      case _ =>
        (Nil, s)

  // whether a statement contains a break of the enclosing loop or switch, not of a nested one
  def breaks(s: Stmt): Boolean =
    s match
      case Break                 => true
      case If(_, left, right)    => breaks(left) || right.exists(breaks)
      case Block(stmts)          => stmts.exists(breaks)
      case Labeled(_, stmt)      => breaks(stmt)
      case Case(_, stmt)         => breaks(stmt)
      case _                     => false

  // the labels of an empty statement that is the last of a function body, i.e. of its end
  def ends(body: Block): Set[String] =
    body.stmts.lastOption.toList.flatMap(endLabels).toSet

  def endLabels(s: Stmt): List[String] =
    s match
      case Labeled(label, Empty) => List(label)
      case Labeled(label, stmt)  => if endLabels(stmt).nonEmpty then label :: endLabels(stmt) else Nil
      case _                     => Nil

  def labels(s: Stmt): Map[String, Stmt] =
    s match
      case Labeled(label, stmt)          => labels(stmt) + (label -> stmt)
      case Block(stmts)                  => stmts.flatMap(labels).toMap
      case If(_, left, right)            => labels(left) ++ right.toList.flatMap(labels)
      case While(_, body)                => labels(body)
      case DoWhile(body, _)              => labels(body)
      case For(_, _, _, body)            => labels(body)
      case Switch(_, body)               => body.flatMap(labels).toMap
      case Case(_, stmt)                 => labels(stmt)
      case _                             => Map()

  // the condition of a loop, whose calls are evaluated at the beginning of each iteration (`check`),
  // which then leaves the loop if the condition is false, and the loop itself runs while true;
  // without calls, the condition is that of the loop
  def guard(scope: Scope, ctx: Ctx, test: Expr): (core.Expr, List[core.Prog]) =
    val (pre, test_) = cond(scope, ctx, test)
    if pre.isEmpty
    then (test_, Nil)
    else (state.exprs.const("true"), pre :+ state.progs.if_(state.exprs.app("not", List(test_)), state.progs.break, skip))

  // whether continue occurs in `prog` outside of nested loops
  def continues(prog: core.Prog): Boolean =
    prog match
      case core.Continue            => true
      case core.Block(_, progs)     => progs.exists(continues)
      case core.If(_, left, right)  => continues(left) || continues(right)
      case core.Choice(progs)       => progs.exists(continues)
      case _                        => false

  // continue leaves the inner loop of a for statement, break additionally sets the flag `brk`
  def exits(brk: core.Var, prog: core.Prog): core.Prog =
    prog match
      case core.Continue            => state.progs.break
      case core.Break               => state.progs.block(Nil, List(state.progs.assign(List(brk), List(state.exprs.const("true"))), state.progs.break))
      case core.Block(locals, progs) => state.progs.block(locals, progs.map(exits(brk, _)))
      case core.If(test, left, right) => state.progs.if_(test, exits(brk, left), exits(brk, right))
      case core.Choice(progs)       => progs.map(exits(brk, _)).reduceRight(state.progs.choice)
      case _                        => prog

  // assignments x op= e and a[i] op= e, where arrays are values that are updated as a whole
  // the arithmetic operators of compound assignments x += e and of increments x++ and decrements x--,
  // which are x = x + e, x = x + 1, and x = x - 1
  val compound =
    Map("+=" -> "+", "-=" -> "-", "*=" -> "*", "/=" -> "/", "%=" -> "%", "&=" -> "&", "|=" -> "|", "^=" -> "^",
        "<<=" -> "<<", ">>=" -> ">>", "++" -> "+", "--" -> "-")

  def assign(scope: Scope, ctx: Ctx, lhs: Expr, op: String, rhs: Expr): List[core.Prog] =
    lhs match
      // only the effects of the value remain
      case Id(x) if op == "=" && scope.contains(x) && unread.contains(scope(x)._1) =>
        val (pre, _, _) = expr(scope, ctx, rhs)
        pre

      // nondeterministic values and results of calls are assigned directly, without temporary variables
      case Id(x) if op == "=" && scope.contains(x) && nondet(rhs, scope(x)._2) =>
        val Call(f, _) = rhs: @unchecked
        List(havoc(f, scope(x)._1))

      case Id(x) if op == "=" && scope.contains(x) && direct(rhs, scope(x)._2) =>
        val Call(f, args) = rhs: @unchecked
        val (pre, args_) = arguments(scope, ctx, f, args)
        pre :+ state.progs.call(f, args_, List(scope(x)._1))

      case Id(x) =>
        Error.report("unknown variable", x):
          require(scope.contains(x))

        val (v, t) = scope(x)
        val (pre, rhs_) =
          if op == "="
          then value(scope, ctx, rhs, t)
          else
            // x op= e is x = x op e, whose result is converted to the type of x
            val (pre, rhs_, rt) = expr(scope, ctx, rhs)
            val (e_, t_) = binary(op, v, t, rhs_, rt)
            (pre, convert(e_, t_, t))

        pre :+ state.progs.assign(List(v), List(rhs_))

      case App("*", List(_)) =>
        Error.raise("the dereference of a pointer is not supported", lhs)

      case Index(_, _) =>
        val elem = lvalue(scope, lhs)
        val (pre2, rhs_, rt) =
          if op == "="
          then
            val (pre, rhs_) = value(scope, ctx, rhs, elem)
            (pre, rhs_, elem)
          else expr(scope, ctx, rhs)

        // a[i] op= e as above
        def update(old: core.Expr) =
          if op == "="
          then rhs_
          else
            val (e_, t_) = binary(op, old, elem, rhs_, rt)
            convert(e_, t_, elem)

        val (pre1, v, array) = store(scope, ctx, lhs, update)

        pre1 ++ pre2 :+ state.progs.assign(List(v), List(array))

      case _ =>
        Error.raise("invalid left hand side of assignment", lhs)

  // the type of an element of an array variable, e.g. a[i][j]
  def lvalue(scope: Scope, lhs: Expr): Type =
    lhs match
      case Id(x) =>
        Error.report("unknown variable", x):
          require(scope.contains(x))
        scope(x)._2

      case Index(base, _) =>
        lvalue(scope, base) match
          case ArrayType(elem) => elem
          case _               => Error.raise("indexing of a variable that is not an array", base)

      case _ =>
        Error.raise("invalid left hand side of assignment", lhs)

  // the new value of the array variable of `lhs`, whose element is updated to `rhs` of its old value,
  // where arrays are values: for nested arrays, the inner array is updated, and then the outer one
  def store(scope: Scope, ctx: Ctx, lhs: Expr, rhs: core.Expr => core.Expr): (List[core.Prog], core.Var, core.Expr) =
    lhs match
      case Id(x) =>
        val (v, _) = scope(x)
        (Nil, v, rhs(v))

      case Index(base, index) =>
        val (pre, index_) = int(scope, ctx, index)
        val (pre_, v, array) = store(scope, ctx, base, base_ => state.exprs.app("store", List(base_, index_, rhs(state.exprs.app("select", List(base_, index_))))))
        (pre_ ++ pre, v, array)

      case _ =>
        Error.raise("invalid left hand side of assignment", lhs)

  // the array variable of an assignment to an element, e.g. a in a[i][j]
  def root(lhs: Expr): Set[String] =
    lhs match
      case Id(x)          => Set(x)
      case Index(base, _) => root(base)
      case _              => Set()

  // the integer type of __VERIFIER_nondet_<typ>, where size_t is unsigned long; None for types whose range is not
  // known, e.g. pointer
  def integer(typ: String): Option[IntType] =
    typ match
      case "char"              => Some(IntType(true, "char"))
      case "uchar"             => Some(IntType(false, "char"))
      case "short"             => Some(IntType(true, "short"))
      case "ushort"            => Some(IntType(false, "short"))
      case "int"               => Some(IntType(true, "int"))
      case "uint" | "unsigned" => Some(IntType(false, "int"))
      case "long"              => Some(IntType(true, "long"))
      case "ulong" | "size_t"  => Some(IntType(false, "long"))
      case "longlong"          => Some(IntType(true, "longlong"))
      case "ulonglong"         => Some(IntType(false, "longlong"))
      case _                   => None

  // a nondeterministic value of __VERIFIER_nondet_<typ>, within the range of its type, as integers are unbounded
  // otherwise; only nonnegative for unsigned types, e.g. uint and size_t, with -unbounded or if the range is unknown;
  // variables declared without a value stay arbitrary
  def havoc(f: String, x: core.Var): core.Prog =
    val typ = f.stripPrefix("__VERIFIER_nondet_")
    integer(typ) match
      case Some(t) if !unbounded =>
        val (lo, hi) = range(t)
        val above = state.exprs.app("<=", List(state.exprs.num(lo), x))
        val below = state.exprs.app("<=", List(x, state.exprs.num(hi)))
        state.progs.spec(List(x), state.exprs.const("true"), state.exprs.app("and", List(above, below)))

      case _ if typ.startsWith("u") || typ == "size_t" =>
        state.progs.spec(List(x), state.exprs.const("true"), state.exprs.app("<=", List(state.exprs.num(0), x)))

      case _ =>
        state.progs.havoc(List(x))

  // the value needs no conversion to type `t`, which it does to an unsigned type of a smaller size, e.g.
  // unsigned char x = __VERIFIER_nondet_int()
  def nondet(rhs: Expr, t: Type) =
    rhs match
      case Call("__VERIFIER_nondet_bool", Nil) => t == BoolType
      case Call(f, Nil) if f.startsWith("__VERIFIER_nondet_") =>
        val from = integer(f.stripPrefix("__VERIFIER_nondet_")).getOrElse(IntType.int)
        t.isInstanceOf[IntType] && fits(from, t)
      case _ => false
      case _                                   => false

  // loops modify the global variables that their body assigns or that the functions it calls modify,
  // which are their modifies clause, as C has no annotations for it
  def while_(test: core.Expr, body: core.Prog): core.Prog =
    def calls(prog: core.Prog): Set[core.Var] =
      prog match
        case core.Call(f, _, _) => state.procattrs(f).modifies.toSet
        case _                  => prog.subprogs.flatMap(calls).toSet

    val vars = globals.values.map(_._1).toSet
    val mod = (body.mod.toSet intersect vars) ++ calls(body)
    val attrs = if mod.isEmpty then Attrs.empty else Attrs(List("modifies" -> Some(mod.toList.sortBy(_.name.toString))))
    state.progs.while_(test, body, attrs)

  // calls of functions whose result has the type of the variable, which needs no conversion
  def direct(rhs: Expr, t: Type) =
    rhs match
      case Call(f, _) => functions.get(f).exists(_.typ == t)
      case _          => false

  // the names assigned in a statement, syntactically, for the parameters that must be copied into locals
  def assigned(s: Stmt): Set[String] =
    s match
      case Assign(lhs, _, rhs)           => root(lhs) ++ writes(lhs) ++ writes(rhs)
      case ExprStmt(e)                   => writes(e)
      case Return(e)                     => e.toSet.flatMap(writes)
      case Decl(_, _, decls)             => decls.flatMap(_.init).toSet.flatMap(writes)
      case If(test, left, right)         => writes(test) ++ assigned(left) ++ right.toSet.flatMap(assigned)
      case While(test, body)             => writes(test) ++ assigned(body)
      case DoWhile(body, test)           => writes(test) ++ assigned(body)
      case For(init, test, step, body)   => init.toSet.flatMap(assigned) ++ test.toSet.flatMap(writes) ++ step.toSet.flatMap(assigned) ++ assigned(body)
      case Loop(test, body, step)        => test.toSet.flatMap(writes) ++ step.toSet.flatMap(assigned) ++ assigned(body)
      case Block(stmts)                  => stmts.toSet.flatMap(assigned)
      case Labeled(_, stmt)              => assigned(stmt)
      case Switch(test, body)            => writes(test) ++ body.toSet.flatMap(assigned)
      case Case(_, stmt)                 => assigned(stmt)
      case _                             => Set()

  // the direct subexpressions of an expression
  def parts(e: Expr): List[Expr] =
    e match
      case Call(_, args)        => args
      case Index(base, index)   => List(base, index)
      case App(_, args)         => args
      case Cast(_, e)           => List(e)
      case Incr(lhs, _, _)      => List(lhs)
      case SizeofExpr(e)        => List(e)
      case Items(items)         => items
      case Cond(test, branches) => test :: branches.toList.flatMap((left, right) => List(left, right))
      case _                    => Nil

  // the functions called in an expression
  def calls(e: Expr): Set[String] =
    e match
      case Call(f, _) => parts(e).toSet.flatMap(calls) + f
      case _          => parts(e).toSet.flatMap(calls)

  // the variables incremented or decremented in an expression
  def writes(e: Expr): Set[String] =
    e match
      case Incr(lhs, _, _) => parts(e).toSet.flatMap(writes) ++ root(lhs)
      case _               => parts(e).toSet.flatMap(writes)

  // the global variables assigned in a function body directly, respecting local declarations that shadow them,
  // and the functions that it calls
  def effects(scope: Set[String], s: Stmt): (Set[String], Set[String]) =
    def global(x: String) =
      if globals.contains(x) && !scope.contains(x) then Set(x) else Set()

    // the global variables incremented in expressions, and the functions they call
    def exprs(es: List[Expr]): (Set[String], Set[String]) =
      (es.toSet.flatMap(writes).flatMap(global), es.toSet.flatMap(calls))

    // iteratively, since the statements of a block may be many, e.g. in the outputs of the reducers of SV-COMP
    def all(scope: Set[String], stmts: List[Stmt]): (Set[String], Set[String]) =
      val (_, mod, called) =
        stmts.foldLeft((scope, Set[String](), Set[String]())):
          case ((scope, mod, called), Decl(_, _, decls)) =>
            val (mod_, called_) = exprs(decls.flatMap(_.init))
            (scope ++ decls.map(_.name), mod ++ mod_, called ++ called_)

          case ((scope, mod, called), stmt) =>
            val (mod_, called_) = effects(scope, stmt)
            (scope, mod ++ mod_, called ++ called_)
      (mod, called)

    s match
      case Assign(lhs, _, rhs)                 =>
        val (mod, called) = exprs(List(lhs, rhs))
        (root(lhs).flatMap(global) ++ mod, called)
      case ExprStmt(e)                         => exprs(List(e))
      case Return(e)                           => exprs(e.toList)
      case If(test, left, right)               => all(scope, List(ExprStmt(test), left) ++ right.toList)
      case While(test, body)                   => all(scope, List(ExprStmt(test), body))
      case DoWhile(body, test)                 => all(scope, List(body, ExprStmt(test)))
      case For(init, test, step, body)         => all(scope, init.toList ++ test.map(ExprStmt(_)).toList ++ step.toList :+ body)
      case Loop(test, body, step)              => all(scope, test.map(ExprStmt(_)).toList ++ step.toList :+ body)
      case Block(stmts)                        => all(scope, stmts)
      case Labeled(_, stmt)                    => all(scope, List(stmt))
      case Switch(test, body)                  => all(scope, ExprStmt(test) :: body)
      case Case(_, stmt)                       => all(scope, List(stmt))
      case decl: Decl                          => all(scope, List(decl))
      case _                                   => (Set(), Set())

  // the global variables modified by each function, directly or by the functions it calls, as a fixpoint
  def modifies(defs: List[Function]): Map[String, Set[String]] =
    val direct =
      for Function(_, f, params, body) <- defs
      yield f -> effects(params.map(_._2).toSet, body.getOrElse(Block(Nil)))

    val calls = direct.toMap.view.mapValues(_._2.filter(functions.contains)).toMap
    var mod = direct.toMap.view.mapValues(_._1).toMap

    var changed = true
    while changed do
      val mod_ =
        for (f, xs) <- mod
        yield f -> (xs ++ calls(f).flatMap(g => mod.getOrElse(g, Set())))
      changed = mod_ != mod
      mod = mod_

    mod

  def resolve(unit: List[Top]): List[core.Cmd] =
    val tops =
      unit.collect:
        case f @ Function(_, name, _, _) if !Syntax.builtin(name) => readonly(f)
        case top if !top.isInstanceOf[Function]                   => top

    // the signatures of all functions are known before any body is resolved
    for case f @ Function(_, name, _, _) <- tops if !functions.contains(name)
    do functions(name) = f

    // the definition of each function, otherwise its last declaration
    val defs =
      for (name, group) <- tops.collect { case f: Function => f }.groupBy(_.name)
      yield name -> group.find(_.body.isDefined).getOrElse(group.last)

    val cmds = mutable.ListBuffer[core.Cmd]()

    // global variables are zero, as in C, which is the precondition of main, the entry point of the program,
    // and their initializers, which may refer to those declared before, are assignments at the beginning of main,
    // such that the program can be printed as C without annotations
    val zeros = mutable.ListBuffer[core.Expr]()
    val inits = mutable.ListBuffer[core.Prog]()

    for case Global(Decl(t, words, decls)) <- tops; Declarator(pointer, x, sizes, init) <- decls
    do
      // global pointers are values, which are null without initializer
      Error.report("arrays of pointers are not supported", x):
        require(!pointer || sizes.isEmpty)

      val t_ = if pointer then PointerType(t) else array(t, sizes)

      for e <- init
      do
        Error.report("initialized global array", x):
          require(sizes.isEmpty || e.isInstanceOf[Items])

        val (progs, e_) = value(globals.toMap, Ctx(None, mutable.ListBuffer()), e, t_)
        Error.report("initial value of global variable must not call functions", x, e):
          require(progs.isEmpty)

        inits += state.progs.assign(List(state.exprs.formal(x, typ(t_))), List(e_))

      zeros += state.exprs.app("=", List(state.exprs.formal(x, typ(t_)), zero(t_)))
      state = state.declare(x, typ(t_), Attrs.empty)
      globals(x) = (state.vars(x), t_)
      if !pointer then declared(state.vars(x)) = (elem(t, words), sizes, init)

    val initialized = inits.toSet.flatMap(_.mod).map(_.name.name)
    val mod = modifies(defs.values.toList).map((f, xs) => if f == "main" then f -> (xs ++ initialized) else f -> xs)

    // the precondition of main that the global variables without initializer are zero,
    // which is type checked here, since the attributes of procedures are not checked with their bodies
    val zeros_ =
      if zeros.isEmpty
      then state.exprs.const("true")
      else
        val phi = zeros.reduce((phi, psi) => state.exprs.app("and", List(phi, psi)))
        state.exprs.check(core.Scope.empty ++ globals.values.map(_._1).toList, phi, state.types.sort("Bool"))

    // procedures are declared before the bodies are resolved, since they may call each other
    for (name, Function(ret, _, params, _)) <- defs
    do
      val in = params.map((t, x) => state.exprs.formal(x, typ(t)))
      val out = if ret == VoidType then Nil else List(state.exprs.formal("result", typ(ret)))
      val mod_ = mod(name).toList.sorted.map(globals(_)._1)
      val modifies = if mod_.isEmpty then Nil else List("modifies" -> Some(mod_))
      val requires = if name == "main" && zeros.nonEmpty then List("requires" -> Some(zeros_)) else Nil
      val attrs = Attrs(modifies ++ requires)

      Error.report("parameter named result", name):
        require(ret == VoidType || !params.exists(_._2 == "result"))

      state = state.declare(name, Nil, in, out, attrs)

    // the commands in the order of the input, where a function is emitted at its definition
    for top <- tops
    do
      top match
        case Global(Decl(_, _, decls)) =>
          for Declarator(_, x, _, _) <- decls
          do cmds += state.cmds.declareVar(x)

        case f @ Function(_, name, _, _) if defs(name) eq f =>
          f.body match
            case None =>
              cmds += state.cmds.declareProc(name)

            case Some(body) =>
              val entry = if name == "main" then inits.toList else Nil
              val body_ = define(f, body, mod(name), entry)
              state = state.define(name, body_)
              cmds += state.cmds.defineProc(name)

        case _ =>

    cmds.toList

  // parameters that are assigned are copied into fresh locals, since the inputs of procedures are fixed,
  // followed by the statements on entry, i.e. the initializers of the global variables for main
  def define(f: Function, body: Block, mod: Set[String], entry: List[core.Prog]): core.Prog =
    val Function(ret, name, params, _) = f
    val core.Proc(_, _, in, out) = state.procs(name)

    val ctx = Ctx(out.headOption.map((_, ret)), mutable.ListBuffer(), labels(body), ends(body))
    val written = assigned(body)

    val copies =
      for ((t, x), v) <- params zip in if written.contains(x)
      yield (x, v, v.fresh, t)

    val scope =
      globals.toMap ++
        (for ((t, x), v) <- params zip in yield x -> (v, t)) ++
        (for (x, _, copy, t) <- copies yield x -> (copy, t))

    val body_ = block(scope, ctx, body.stmts, body = true)
    val init = for (_, v, copy, _) <- copies yield state.progs.assign(List(copy), List(v))
    val prog = state.progs.block(copies.map(_._3) ++ ctx.temps.toList, init ++ entry :+ body_)

    val fixed = in.toSet ++ (globals.values.map(_._1).toSet -- mod.map(globals(_)._1))
    val scope_ = core.Scope.empty ++ globals.values.map(_._1).toList ++ in ++ out
    state.progs.check(scope_, fixed, mod.map(globals(_)._1), prog)
