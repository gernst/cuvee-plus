package cuvee.c

import scala.collection.mutable

import cuvee.Error
import cuvee.core
import cuvee.core.State
import cuvee.core.Attrs
import cuvee.sexpr

// resolution of a C translation unit into core procedures:
// integer types are Int (unbounded), _Bool is Bool, arrays are values of type Array Int T;
// functions are procedures whose result is the output `result`,
// and whose global variables modified, directly or by calls, are inferred, or those of their assigns clauses;
// calls inside expressions are evaluated before the statement that contains them, in order
// `arch` is the data model, 32 or 64 bit Linux (ILP32 or LP64), see Config.arch;
// `unbounded` drops the ranges of the types of nondeterministic values, see Config.unbounded;
// `infer` infers the global variables that functions and loops modify also if they have assigns or loop assigns
// clauses, as -teq and -chc do (see Source), otherwise those of the clauses are their modifies clauses (see assigned)
class Parser(var state: State, arch: Int, unbounded: Boolean, infer: Boolean):
  // the signatures of the functions by name
  val functions = mutable.Map[String, Function]()

  // the functions of math.h without a body (Syntax.math), which are pure, as uninterpreted functions of their
  // arguments rather than procedures, e.g. sqrt (see floats)
  val pure = mutable.Set[String]()

  // the logic functions and predicates of ACSL by name (see logic)
  val logics = mutable.Map[String, LogicFun]()

  // the global variables with their C types
  val globals = mutable.Map[String, (core.Var, Type)]()

  // the declared variables that sizeof may measure: the size of their elements in bytes, the sizes of their arrays,
  // and their initializers (see bytes)
  val declared = mutable.Map[core.Var, (BigInt, List[Option[Expr]], Option[Expr])]()

  // the local pointers that are never read, e.g. char *s; s = in; for an array in, whose assignments are dropped,
  // since other pointers than allocations are no arrays
  val unread = mutable.Set[core.Var]()

  // the context of a function body: its result, the temporary variables for the results of calls,
  // the statements of its labels, which a goto may resolve in its place, and the labels at its end;
  // the clauses of ACSL of the loop that is translated next, but not of the loops nested in it (see loop);
  // the name of the function, for the locations of its loops (see location)
  case class Ctx(result: Option[(core.Var, Type)], temps: mutable.ListBuffer[core.Var],
                 labels: Map[String, Stmt] = Map(), ends: Set[String] = Set(), loop: List[Clause] = Nil,
                 function: String = "")

  type Scope = Map[String, (core.Var, Type)]

  // the environment of the terms of ACSL: the result of the function, \result in a postcondition, in the clauses
  // of a loop, the copies of the variables at its entry, \at(x, LoopEntry), which are assigned before it (see loop),
  // and the variables bound by the quantifiers around a term, which have no copies
  case class Env(result: Option[(core.Var, Type)], entry: Option[(Ctx, mutable.LinkedHashMap[core.Var, core.Var])],
                 bound: Set[core.Var] = Set())

  object Env:
    val empty = Env(None, None)

  def typ(t: Type): core.Type =
    t match
      case IntType(_, _) | Integer => state.types.sort("Int")
      case BoolType     => state.types.sort("Bool")
      case ArrayType(e) => state.types.sort("Array", List(state.types.sort("Int"), typ(e)))
      case VoidType     => Error.raise("void is not a type of values")
      case FloatType(kind) => floats(); state.types.sort(floatSort(kind))

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
      case Some(Call("malloc" | "safe_malloc" | "safe_malloc_or_loop" | "alloca", List(size))) if sizes.isEmpty && elements(size) =>
        (ArrayType(t), None)

      case Some(Call("calloc" | "safe_calloc" | "safe_calloc_or_loop", List(_, size))) if sizes.isEmpty && strip(size).isInstanceOf[SizeofType] =>
        (ArrayType(t), Some(Items(Nil)))

      // other pointers are values, e.g. int *p = NULL, which cannot be dereferenced
      case _ =>
        Error.report("arrays of pointers are not supported", x):
          require(sizes.isEmpty)
        (PointerType(t), init)

  def zero(t: Type): core.Expr =
    t match
      case IntType(_, _) | Integer => state.exprs.num(0)
      case BoolType     => state.exprs.const("false")
      case ArrayType(e) => state.exprs.app("const", List(zero(e)))
      case PointerType(_) => state.exprs.const("null")
      case VoidType     => Error.raise("void is not a type of values")
      case FloatType(kind) => float(kind, "of_int", state.exprs.num(0))

  def temp(ctx: Ctx, t: Type): core.Var =
    val x = state.exprs.formal("tmp", typ(t)).fresh
    ctx.temps += x
    x

  // conversions between integers and truth values as in C
  def toInt(expr: core.Expr, t: Type): core.Expr =
    t match
      case IntType(_, _) | Integer => expr
      case BoolType => state.exprs.app("number", List(expr))
      // truncation towards zero, undefined out of range, hence any integer
      case FloatType(kind) => float(kind, "to_int", expr)
      case _        => Error.raise("not an integer", expr)

  def toBool(expr: core.Expr, t: Type): core.Expr =
    t match
      case BoolType => expr
      case IntType(_, _) | Integer => state.exprs.app("truth", List(expr))
      case PointerType(_) => state.exprs.app("not", List(state.exprs.app("=", List(expr, state.exprs.const("null")))))
      case FloatType(kind) => state.exprs.app("not", List(float(kind, "eq", expr, zero(FloatType(kind)))))
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

  // floating point numbers as uninterpreted sorts Float and Double, whose operations are declared functions, e.g.
  // Double_add and Double_lt, with the conversions Double_of_int, Double_to_int, Float_of_Double, Double_of_Float, and
  // the literals that are no integers Double_lit(num, den); sound for proofs, as IEEE floating point numbers are one
  // interpretation of them, but no counterexample through them is genuine, hence they are :abstract, as the bit
  // operations of the prelude, for which the solver answers unknown rather than incorrect (see smtlib.Solver); declared
  // at their first use, and emitted before the commands of the translation unit (see unit)
  var floating = false

  val freely = Attrs(List("abstract" -> None))

  def floatSort(kind: String): String =
    if kind == "float" then "Float" else "Double"

  def floats(): Unit =
    if !floating
    then
      floating = true
      val int = state.types.sort("Int")
      val bool = state.types.sort("Bool")
      for s <- List("Float", "Double") do state = state.declare(s, 0, Attrs.empty)
      for (name, args, res) <- Syntax.floats
      do
        val formals = args.zipWithIndex.map((t, i) => state.exprs.formal("x" + i, if t == "Int" then int else if t == "Bool" then bool else state.types.sort(t)))
        state = state.declare(name, Nil, formals, if res == "Int" then int else if res == "Bool" then bool else state.types.sort(res), freely)

  def float(kind: String, op: String, args: core.Expr*): core.Expr =
    floats()
    state.exprs.app(floatSort(kind) + "_" + op, args.toList)

  // a literal, e.g. 2.0 as Double_of_int(2), as conversions of integers round to the nearest value like literals,
  // 0.5f as Float_lit(1, 2)
  def floatLiteral(text: String): (core.Expr, Type) =
    val kind = if text.endsWith("f") || text.endsWith("F") then "float" else "double"
    val digits = text.stripSuffix("f").stripSuffix("F").stripSuffix("l").stripSuffix("L")
    val value =
      Error.report("unsupported floating point literal", text):
        BigDecimal(digits)
    val e =
      if value.isWhole
      then float(kind, "of_int", state.exprs.num(value.toBigInt))
      else
        val v = value.bigDecimal.stripTrailingZeros
        val den = BigInt(10).pow(v.scale)
        float(kind, "lit", state.exprs.num(BigInt(v.unscaledValue)), state.exprs.num(den))
    (e, FloatType(kind))

  // the common type of the operands of an arithmetic operator: double if one is, float if one is, otherwise the
  // integer type of the usual arithmetic conversions
  def arithmetic(lt: Type, rt: Type): Type =
    (lt, rt) match
      case (FloatType("double"), _) | (_, FloatType("double")) => FloatType("double")
      case (FloatType(_), _) | (_, FloatType(_))               => FloatType("float")
      case _                                                   => common(lt, rt)

  // a value of type `from` converted to the arithmetic type `to`, as in C
  def cast(e: core.Expr, from: Type, to: Type): core.Expr =
    (from, to) match
      case (FloatType(k), FloatType(l)) if k == l => e
      case (FloatType(k), FloatType(l))           => state.exprs.app(floatSort(l) + "_of_" + floatSort(k), List(e))
      case (_, FloatType(l))                      => float(l, "of_int", toInt(e, from))
      case _                                      => convert(toInt(e, from), from, to)

  // the result of an arithmetic operator in the integer type `t`, which wraps around for unsigned types after
  // additions, subtractions, multiplications, and shifts left; quotients, remainders, and shifts right of values
  // within the range stay within it, and the bit operations are declared only
  def wrap(op: String, e: core.Expr, t: IntType): core.Expr =
    (op, overflow(t)) match
      case ("+" | "-" | "*" | "<<", Some(f)) => state.exprs.app(f, List(e))
      case _                                 => e

  // a binary arithmetic operator applied to the operands converted to their common type, which is the type of the
  // result, where shifts have the promoted type of their left operand, whose right operand is not converted
  def binary(op: String, left: core.Expr, lt: Type, right: core.Expr, rt: Type): (core.Expr, Type) =
    arithmetic(lt, rt) match
      case t @ FloatType(kind) =>
        val name = op match
          case "+" => "add"
          case "-" => "sub"
          case "*" => "mul"
          case "/" => "div"
          case _   => Error.raise("operator on floating point numbers", op)
        (float(kind, name, cast(left, lt, t), cast(right, rt, t)), t)
      case _ => binary_(op, left, lt, right, rt)

  def binary_(op: String, left: core.Expr, lt: Type, right: core.Expr, rt: Type): (core.Expr, IntType) =
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

      case FloatNum(text) =>
        val (e_, t) = floatLiteral(text)
        (Nil, e_, t)

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
        val t = nondetType(f)
        val x = temp(ctx, t)
        (List(havoc(f, x)), x, t)

      case Call(f, args) if pure.contains(f) =>
        val (pre, args_) = arguments(scope, ctx, f, args)
        (pre, state.exprs.app(f, args_), functions(f).typ)

      case Call(f, args) =>
        val (pre, args_) = arguments(scope, ctx, f, args)
        val ret = functions(f).typ

        Error.report("call of a void function inside an expression", f):
          require(ret != VoidType)

        val x = temp(ctx, ret)
        (pre :+ state.progs.call(f, args_, List(x)), x, ret)

      case App("-", List(arg)) =>
        val (pre, arg_, t) = expr(scope, ctx, arg)
        t match
          case FloatType(kind) =>
            (pre, float(kind, "neg", arg_), t)
          case _ =>
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
            arithmetic(lt, rt) match
              case t @ FloatType(kind) => float(kind, "eq", cast(left_, lt, t), cast(right_, rt, t))
              case t                   => state.exprs.app("=", List(cast(left_, lt, t), cast(right_, rt, t)))

        (pre1 ++ pre2, if op == "==" then eq else state.exprs.app("not", List(eq)), BoolType)

      // in the common type of the operands, e.g. -1 < 1u is false, as -1 is converted to unsigned int
      case App(op @ ("<" | "<=" | ">" | ">="), List(left, right)) =>
        val (pre1, left0, lt) = expr(scope, ctx, left)
        val (pre2, right0, rt) = expr(scope, ctx, right)
        val t = arithmetic(lt, rt)
        val left_ = cast(left0, lt, t)
        val right_ = cast(right0, rt, t)

        val phi = (op, t) match
          case ("<", FloatType(kind))  => float(kind, "lt", left_, right_)
          case ("<=", FloatType(kind)) => float(kind, "le", left_, right_)
          case (">", FloatType(kind))  => float(kind, "lt", right_, left_)
          case (_, FloatType(kind))    => float(kind, "le", right_, left_)
          case ("<", _)  => state.exprs.app("<", List(left_, right_))
          case ("<=", _) => state.exprs.app("<=", List(left_, right_))
          case (">", _)  => state.exprs.app(">", List(left_, right_))
          case _         => state.exprs.app(">=", List(left_, right_))

        (pre1 ++ pre2, phi, BoolType)

      case App(op, List(left, right)) =>
        val (pre1, left_, lt) = expr(scope, ctx, left)
        val (pre2, right_, rt) = expr(scope, ctx, right)
        val (e_, t) = logical(op, left_, lt, right_, rt).getOrElse(binary(op, left_, lt, right_, rt))
        (pre1 ++ pre2, e_, t)

      case Cond(e, None) =>
        expr(scope, ctx, e)

      // casts to signed integer types are the identity, as integers are unbounded, those to unsigned types wrap around
      case Cast(t: IntType, e) =>
        val (pre, e_, t_) = expr(scope, ctx, e)
        (pre, cast(e_, t_, t), t)

      case Cast(t: FloatType, e) =>
        val (pre, e_, t_) = expr(scope, ctx, e)
        (pre, cast(e_, t_, t), t)

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

      case Result | Old(_) | At(_, _) | Valid | Quant(_, _, _) | Locations(_) =>
        Error.raise("term of ACSL outside of an annotation", e)

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
            val t = arithmetic(lt, rt)
            (t, cast(left_, lt, t), cast(right_, rt, t))

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
      case IntType(_, _) | FloatType(_) =>
        val (pre, e_, t_) = expr(scope, ctx, e)
        (pre, cast(e_, t_, t))
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

  // the terms of ACSL, whose arithmetic is on the mathematical integers, without the conversions and wrap-around of C,
  // whose comparisons chain, 0 <= i < n, and whose quantified variables of C types range over these types, unless
  // -unbounded (see bounds)
  def term(scope: Scope, env: Env, e: Expr): (core.Expr, Type) =
    e match
      case Num(text) =>
        (state.exprs.num(literal(text)), Integer)

      case Id("true") if !scope.contains("true") =>
        (state.exprs.const("true"), BoolType)

      case Id("false") if !scope.contains("false") =>
        (state.exprs.const("false"), BoolType)

      case Id(x) =>
        Error.report("unknown variable", x):
          require(scope.contains(x))
        scope(x)

      case Result =>
        Error.report("\\result outside of a postcondition"):
          require(env.result.isDefined)
        env.result.get

      case Old(arg) =>
        val (arg_, t) = term(scope, env, arg)
        (state.exprs.old(arg_), t)

      case At(arg, "Pre") =>
        term(scope, env, Old(arg))

      case At(arg, "Here") =>
        term(scope, env, arg)

      // the variables of the term are replaced by their copies at the entry of the loop
      case At(arg, "LoopEntry") =>
        Error.report("\\at(_, LoopEntry) outside of the clauses of a loop", arg):
          require(env.entry.isDefined)
        val Some((ctx, copies)) = env.entry: @unchecked
        val (arg_, t) = term(scope, env, arg)
        val xs = arg_.free.toList.filter(x => scope.values.exists(_._1 == x) && !env.bound.contains(x))
        val ys = for x <- xs yield copies.getOrElseUpdate(x, temp(ctx, scope.values.find(_._1 == x).get._2))
        (core.Subst.from(xs, ys)(arg_), t)

      case At(_, label) =>
        Error.raise("label of \\at not supported", label)

      case Valid =>
        (state.exprs.const("true"), BoolType)

      case Index(base, index) =>
        val (base_, t) = term(scope, env, base)
        val (index_, it) = term(scope, env, index)
        t match
          case ArrayType(elem) => (state.exprs.app("select", List(base_, toInt(index_, it))), elem)
          case _               => Error.raise("indexing of an expression that is not an array", base)

      case Cond(e, None) =>
        term(scope, env, e)

      case Cond(test, Some((left, right))) =>
        val test_ = predicate(scope, env, test)
        val (left_, lt) = term(scope, env, left)
        val (right_, rt) = term(scope, env, right)
        if lt == BoolType && rt == BoolType
        then (state.exprs.app("ite", List(test_, left_, right_)), BoolType)
        else (state.exprs.app("ite", List(test_, toInt(left_, lt), toInt(right_, rt))), Integer)

      case App("!", List(arg)) =>
        (state.exprs.app("not", List(predicate(scope, env, arg))), BoolType)

      case App("-", List(arg)) =>
        val (arg_, t) = term(scope, env, arg)
        (state.exprs.app("-", List(toInt(arg_, t))), Integer)

      case App("~", List(arg)) =>
        val (arg_, t) = term(scope, env, arg)
        (state.exprs.app("bitnot", List(toInt(arg_, t))), Integer)

      case App(op @ ("&&" | "||" | "==>" | "<==>"), List(left, right)) =>
        val fun = op match
          case "&&"  => "and"
          case "||"  => "or"
          case "==>" => "=>"
          case _     => "="
        (state.exprs.app(fun, List(predicate(scope, env, left), predicate(scope, env, right))), BoolType)

      // chained comparisons, where a parenthesized comparison is Cond(_, None) and does not chain
      case App(op, List(App(op_, List(_, middle)), right)) if relation(op) && relation(op_) =>
        val App(_, List(first, _)) = e: @unchecked
        val left = predicate(scope, env, first)
        val next = predicate(scope, env, App(op, List(middle, right)))
        (state.exprs.app("and", List(left, next)), BoolType)

      case App(op, List(left, right)) if relation(op) =>
        val (left_, lt) = term(scope, env, left)
        val (right_, rt) = term(scope, env, right)
        val (left__, right__) =
          (lt, rt) match
            case (BoolType, BoolType) | (ArrayType(_), _) | (_, ArrayType(_)) => (left_, right_)
            case _                                                          => (toInt(left_, lt), toInt(right_, rt))
        val phi = op match
          case "==" => state.exprs.app("=", List(left__, right__))
          case "!=" => state.exprs.app("not", List(state.exprs.app("=", List(left__, right__))))
          case _    => state.exprs.app(op, List(left__, right__))
        (phi, BoolType)

      case App(op, List(left, right)) =>
        val (left_, lt) = term(scope, env, left)
        val (right_, rt) = term(scope, env, right)
        logical(op, left_, lt, right_, rt).getOrElse((arith(op, toInt(left_, lt), toInt(right_, rt)), Integer))

      case Cast(Integer, e) =>
        val (e_, t) = term(scope, env, e)
        (toInt(e_, t), Integer)

      case Cast(t: IntType, e) =>
        val (e_, t_) = term(scope, env, e)
        (convert(toInt(e_, t_), t_, t), t)

      case Cast(BoolType, e) =>
        (predicate(scope, env, e), BoolType)

      // calls of logic functions, whose arguments are converted to the types of the parameters
      case Call(f, args) if logics.contains(f) =>
        val LogicFun(t, _, params, _) = logics(f)
        Error.report("wrong number of arguments", f, args):
          require(params.length == args.length)
        val args_ =
          for ((pt, _), arg) <- params zip args
          yield
            val (arg_, at) = term(scope, env, arg)
            coerce(arg_, at, values(pt))
        (state.exprs.app(f, args_), values(t))

      // quantified pointers are arrays, as the parameters of logic functions (see values)
      case Quant(quant, bound, body) =>
        val xs = for (t, x) <- bound yield (x, state.exprs.formal(x, typ(values(t))), values(t))
        val scope_ = scope ++ xs.map((x, v, t) => x -> (v, t))
        val body_ = predicate(scope_, env.copy(bound = env.bound ++ xs.map(_._2)), body)
        val guards = xs.flatMap((_, v, t) => bounds(t, v))
        val guard = if guards.isEmpty then None else Some(guards.reduce((phi, psi) => state.exprs.app("and", List(phi, psi))))
        val vs = xs.map(_._2)
        quant match
          case "forall" => (state.exprs.all(vs, guard.fold(body_)(g => state.exprs.app("=>", List(g, body_)))), BoolType)
          case _        => (state.exprs.ex(vs, guard.fold(body_)(g => state.exprs.app("and", List(g, body_)))), BoolType)

      case _ =>
        Error.raise("not supported in annotations", e)

  // the pointers of the signatures of logic functions and of quantified variables are the arrays they point to,
  // since arrays are values, e.g. int *a and int **m for the arrays int a[] and int m[][]
  def values(t: Type): Type =
    t match
      case PointerType(elem) => ArrayType(values(elem))
      case ArrayType(elem)   => ArrayType(values(elem))
      case _                 => t

  // a term of type `from` as one of type `to`, e.g. the argument of a logic function
  def coerce(e: core.Expr, from: Type, to: Type): core.Expr =
    to match
      case BoolType                => toBool(e, from)
      case IntType(_, _) | Integer => toInt(e, from)
      case _                       => e

  def relation(op: String) =
    op == "==" || op == "!=" || op == "<" || op == "<=" || op == ">" || op == ">="

  def predicate(scope: Scope, env: Env, e: Expr): core.Expr =
    val (e_, t) = term(scope, env, e)
    toBool(e_, t)

  // the range of a quantified variable of a C integer type, as that of nondeterministic values (see havoc)
  def bounds(t: Type, x: core.Var): Option[core.Expr] =
    t match
      case t: IntType if !unbounded =>
        val (lo, hi) = range(t)
        Some(state.exprs.app("and", List(state.exprs.app("<=", List(state.exprs.num(lo), x)), state.exprs.app("<=", List(x, state.exprs.num(hi))))))
      case t: IntType if !t.signed =>
        Some(state.exprs.app("<=", List(state.exprs.num(0), x)))
      case _ =>
        None

  // a predicate of an annotation, type checked in the scope of the C variables, since the attributes of loops and
  // procedures are not checked with the bodies
  def formula(scope: Scope, env: Env, phi: Expr): core.Expr =
    val vars = scope.values.map(_._1).toList ++ env.result.map(_._1)
    state.exprs.check(core.Scope.empty ++ vars, predicate(scope, env, phi), state.types.sort("Bool"))

  def measure(scope: Scope, env: Env, e: Expr): core.Expr =
    val vars = scope.values.map(_._1).toList ++ env.result.map(_._1)
    val (e_, t) = term(scope, env, e)
    state.exprs.check(core.Scope.empty ++ vars, toInt(e_, t), state.types.sort("Int"))

  // the clauses of ACSL as the attributes of loops and procedures; assigns and loop assigns are the modifies clauses
  // instead (see assigned)
  def clauses(scope: Scope, env: Env, clauses: List[Clause]): List[(String, Option[core.Expr])] =
    clauses.collect:
      case Clause("requires", Some(phi))       => "requires" -> Some(formula(scope, env.copy(result = None), phi))
      case Clause("ensures", Some(phi))        => "ensures" -> Some(formula(scope, env, phi))
      case Clause("decreases", Some(e))        => "decreases" -> Some(measure(scope, env.copy(result = None), e))
      case Clause("loop invariant", Some(phi)) => "invariant" -> Some(formula(scope, env, phi))
      case Clause("loop variant", Some(e))     => "decreases" -> Some(measure(scope, env, e))

  // the global variables of the assigns or loop assigns clauses of `kind` among `clauses`, which are the modifies
  // clause of a function or loop; None if there are none or if the modified variables are inferred; the local
  // variables among them are dropped, since the transforms infer them from the bodies
  def assigned(scope: Scope, clauses: List[Clause], kind: String): Option[List[core.Var]] =
    val names = clauses.collect { case Clause(`kind`, Some(Locations(xs))) => xs }
    if infer || names.isEmpty
    then None
    else
      val xs = names.flatten.distinct
      val unknown = xs.filterNot(scope.contains)
      if unknown.nonEmpty then Error.raise(kind + " lists variables that are not in scope", unknown)
      val vars = globals.values.map(_._1).toSet
      Some(xs.map(scope(_)._1).filter(vars).sortBy(_.name.toString))

  // the clauses of the loop that is translated, in its scope (see Ctx), the assignments of the copies of the
  // variables at its entry before it, and the global variables of its loop assigns (see assigned); the ranges of
  // the variables of unsigned types that it modifies, which Frama-C/WP assumes, are no implicit invariants, they
  // must be stated by loop invariants
  def loop(scope: Scope, ctx: Ctx): (List[core.Prog], List[(String, Option[core.Expr])], Option[List[core.Var]]) =
    if ctx.loop.isEmpty
    then (Nil, Nil, None)
    else
      val copies = mutable.LinkedHashMap[core.Var, core.Var]()
      val clauses_ = clauses(scope, Env(None, Some((ctx, copies))), ctx.loop)
      val pre = for (x, y) <- copies.toList yield state.progs.assign(List(y), List(x))
      (pre, clauses_, assigned(scope, ctx.loop, "loop assigns"))

  // the bit operations on truth values, e.g. (z > 100) & (x < 100), are the logical ones, whose operands are 0 or 1
  def logical(op: String, left: core.Expr, lt: Type, right: core.Expr, rt: Type): Option[(core.Expr, Type)] =
    (op, lt, rt) match
      case ("&", BoolType, BoolType) => Some((state.exprs.app("and", List(left, right)), BoolType))
      case ("|", BoolType, BoolType) => Some((state.exprs.app("or", List(left, right)), BoolType))
      case ("^", BoolType, BoolType) => Some((state.exprs.app("not", List(state.exprs.app("=", List(left, right)))), BoolType))
      case _                         => None

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
      case Annotated(clauses, loop)      => clauses.flatMap(_.arg).toSet.flatMap(indexed) ++ indexed(loop)
      case Assertion(phi)                => indexed(phi)
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
      case Annotated(clauses, loop)      => clauses.flatMap(_.arg).toSet.flatMap(reads) ++ reads(loop)
      case Assertion(phi)                => reads(phi)
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

      // exit ends the program, the error is not reached afterwards, whatever the exit code
      case ExprStmt(Call("exit", List(code))) =>
        val (pre, _, _) = expr(scope, ctx, code)
        pre :+ state.progs.assume(state.exprs.const("false"))

      // calls as statements, whose result is discarded
      case ExprStmt(Call(f, args)) if pure.contains(f) =>
        arguments(scope, ctx, f, args)._1

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

      case w @ While(test, body) =>
        val (test_, check) = guard(scope, ctx, test)
        val body_ = wrap(check ++ stmt(scope, ctx.copy(loop = Nil), body))
        val (pre, clauses, assigns) = loop(scope, ctx)
        pre :+ while_(test_, body_, clauses, assigns, List(location(ctx, w.at)))

      // the test is evaluated after each iteration, also after continue, but not before the first one
      case d @ DoWhile(body, test) =>
        val (test_, check) = guard(scope, ctx, test)
        val first = temp(ctx, BoolType)

        val body_ =
          if check.isEmpty
          then state.progs.block(Nil, state.progs.assign(List(first), List(state.exprs.const("false"))) :: stmt(scope, ctx.copy(loop = Nil), body))
          else state.progs.block(Nil, state.progs.if_(state.exprs.app("not", List(first)), state.progs.block(Nil, check), skip) :: state.progs.assign(List(first), List(state.exprs.const("false"))) :: stmt(scope, ctx.copy(loop = Nil), body))

        val (pre, clauses, assigns) = loop(scope, ctx)
        pre ++ List(state.progs.assign(List(first), List(state.exprs.const("true"))), while_(state.exprs.app("or", List(first, test_)), body_, clauses, assigns, List(location(ctx, d.at))))

      // the initialization may declare variables, whose scope is the loop
      case f @ For(init, test, step, body) =>
        List(block(scope, ctx, init.toList :+ Loop(test, body, step)(f.at)))

      // continue must execute the step, which precedes it (see stepped), so that the loop stays a single loop
      case l @ Loop(test, body, step) =>
        val (test_, check) = test.map(guard(scope, ctx, _)).getOrElse((state.exprs.const("true"), Nil))
        val body_ = stmt(scope, ctx.copy(loop = Nil), body)
        val step_ = step.toList.flatMap(stmt(scope, ctx, _))
        val block = state.progs.block(Nil, check ++ body_.map(stepped(step_, _)) ++ step_)
        val (pre, clauses, assigns) = loop(scope, ctx)
        pre :+ while_(test_, block, clauses, assigns, List(location(ctx, l.at)))

      // the clauses of the loop are resolved in its scope, e.g. with the variables declared by the initialization of a for
      case Annotated(clauses, loop) =>
        stmt(scope, ctx.copy(loop = clauses), loop)

      case Assertion(phi) =>
        List(state.progs.assert(formula(scope, Env.empty, phi)))

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
      case Annotated(_, loop)            => unlabeled(loop)
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
      case Annotated(_, loop)            => labels(loop)
      case _                             => Map()

  // whether a statement contains annotations of ACSL
  def acsl(s: Stmt): Boolean =
    s match
      case Annotated(_, _) | Assertion(_) => true
      case Block(stmts)                   => stmts.exists(acsl)
      case If(_, left, right)             => acsl(left) || right.exists(acsl)
      case While(_, body)                 => acsl(body)
      case DoWhile(body, _)               => acsl(body)
      case For(_, _, _, body)             => acsl(body)
      case Labeled(_, stmt)               => acsl(stmt)
      case Switch(_, body)                => body.exists(acsl)
      case Case(_, stmt)                  => acsl(stmt)
      case _                              => false

  // the condition of a loop, whose calls are evaluated at the beginning of each iteration (`check`),
  // which then leaves the loop if the condition is false, and the loop itself runs while true;
  // without calls, the condition is that of the loop
  def guard(scope: Scope, ctx: Ctx, test: Expr): (core.Expr, List[core.Prog]) =
    val (pre, test_) = cond(scope, ctx, test)
    if pre.isEmpty
    then (test_, Nil)
    else (state.exprs.const("true"), pre :+ state.progs.if_(state.exprs.app("not", List(test_)), state.progs.break, skip))

  // the continues of a for statement, outside of nested loops, preceded by its step `step`, which is translated once;
  // without a step, continue stays as it is
  def stepped(step: List[core.Prog], prog: core.Prog): core.Prog =
    prog match
      case core.Continue if step.nonEmpty => state.progs.block(Nil, step :+ state.progs.continue)
      case core.Block(locals, progs, _)   => state.progs.block(locals, progs.map(stepped(step, _)))
      case core.If(test, left, right)     => state.progs.if_(test, stepped(step, left), stepped(step, right))
      case core.Choice(progs)             => progs.map(stepped(step, _)).reduceRight(state.progs.choice)
      case _                              => prog

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
            (pre, cast(e_, t_, t))

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
        nondetType(f) match
          case from: FloatType => t == from
          case from            => t.isInstanceOf[IntType] && fits(from, t)
      case _ => false

  // the type of the values of a nondet function, e.g. double for __VERIFIER_nondet_double
  def nondetType(f: String): Type =
    f.stripPrefix("__VERIFIER_nondet_") match
      case "bool"                => BoolType
      case kind @ ("float" | "double") => FloatType(kind)
      case name                  => integer(name).getOrElse(IntType.int)

  // loops have a modifies clause only if they have loop assigns (see assigned), otherwise they modify what their body
  // modifies (see Type.check); followed by the clauses of ACSL (see loop) and the location of the loop in the source
  // (see location)
  def while_(test: core.Expr, body: core.Prog, clauses: List[(String, Option[core.Expr])] = Nil, assigns: Option[List[core.Var]] = None,
             location: List[(String, Option[Any])] = Nil): core.Prog =
    val attrs = assigns.toList.map(xs => "modifies" -> Some(xs.sortBy(_.name.toString)))
    state.progs.while_(test, body, Attrs(attrs ++ clauses ++ location))

  // the attribute :location (line column function) of a loop whose keyword is at `at`, for the locations of
  // witnesses; an s-expression, which the printers of all languages print and the SMT-LIB parser reads back
  def location(ctx: Ctx, at: (Int, Int)): (String, Option[Any]) =
    val (line, column) = at
    "location" -> Some(List(sexpr.Num(line.toString), sexpr.Num(column.toString), sexpr.Id(ctx.function)))

  // calls of functions whose result has the type of the variable, which needs no conversion
  def direct(rhs: Expr, t: Type) =
    rhs match
      case Call(f, _) => functions.get(f).exists(_.typ == t) && !pure.contains(f)
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
      case Annotated(_, loop)            => assigned(loop)
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
      case Old(e)               => List(e)
      case At(e, _)             => List(e)
      case Quant(_, _, body)    => List(body)
      case _                    => Nil

  // the variables incremented or decremented in an expression
  def writes(e: Expr): Set[String] =
    e match
      case Incr(lhs, _, _) => parts(e).toSet.flatMap(writes) ++ root(lhs)
      case _               => parts(e).toSet.flatMap(writes)

  // the global declarations of ACSL: logic functions and predicates are functions, defined by their body if they
  // have one, which may call them recursively, axioms are axioms, and lemmas are free lemmas, which are trusted,
  // since their proofs need induction in general, both named; their terms cannot refer to the variables of the program
  def logic(top: Top): List[core.Cmd] =
    top match
      case f @ LogicFun(t, name, params, body) =>
        Error.report("logic function named like a function of the program", name):
          require(!functions.contains(name))
        Error.report("logic function already declared", name):
          require(!logics.contains(name))

        val formals = params.map((pt, x) => state.exprs.formal(x, typ(values(pt))))
        state = state.declare(name, Nil, formals, typ(values(t)), Attrs.empty)
        logics(name) = f

        body match
          case None =>
            List(state.cmds.declareFun(name, formals.length))

          case Some(e) =>
            val scope = (for ((pt, x), v) <- params zip formals yield x -> (v, values(pt))).toMap
            val (e_, et) = term(scope, Env.empty, e)
            val body_ = state.exprs.check(core.Scope.empty ++ formals, coerce(e_, et, values(t)), typ(values(t)))
            state = state.define(name, formals.length, body_)
            List(state.cmds.defineFun(name, formals.length))

      case Property(kind, name, phi) =>
        val phi_ = formula(Map(), Env.empty, phi)
        val named = "named" -> Some(sexpr.Id(name))
        if kind == "axiom"
        then List(state.cmds.axiom(Nil, phi_, Attrs(List(named))))
        else List(state.cmds.lemma(Nil, phi_, Attrs(List("free" -> None, named))))

      case _ =>
        Nil

  def resolve(unit: List[Top]): List[core.Cmd] =
    // the declarations of an annotation of ACSL in its place
    val unit_ =
      unit.flatMap:
        case Logical(decls) => decls
        case top            => List(top)

    val tops =
      unit_.collect:
        case f @ Function(_, name, _, _) if !Syntax.builtin(name) => readonly(f)
        case top if !top.isInstanceOf[Function]                   => top

    // the contracts of ACSL by the names of the functions that follow them, those of declarations and of the
    // definition together, where repeated clauses count once
    val contracts = mutable.Map[String, List[Clause]]()
    for case (Contract(clauses), next) <- unit_ zip (unit_.tail.map(Some(_)) :+ None)
    do
      next match
        case Some(Function(_, name, _, _)) => contracts(name) = (contracts.getOrElse(name, Nil) ++ clauses).distinct
        case _                             => Error.raise("contract not followed by a function", clauses)

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

    // the precondition of main that the global variables without initializer are zero,
    // which is type checked here, since the attributes of procedures are not checked with their bodies
    val zeros_ =
      if zeros.isEmpty
      then state.exprs.const("true")
      else
        val phi = zeros.reduce((phi, psi) => state.exprs.app("and", List(phi, psi)))
        state.exprs.check(core.Scope.empty ++ globals.values.map(_._1).toList, phi, state.types.sort("Bool"))

    // the declarations of ACSL in their order before the contracts of the procedures, which may refer to them
    val logical = mutable.Queue.from(tops.collect { case top @ (_: LogicFun | _: Property) => logic(top) })

    // the modifies clauses of the assigns clauses of ACSL by function, main also modifies the global variables that it
    // initializes; the others are inferred from the bodies (see modifies)
    val assigns = mutable.Map[String, List[core.Var]]()

    // procedures are declared before the bodies are resolved, since they may call each other; parameters that shadow
    // global variables are renamed apart, as local variables are (see block)
    for (name, f) <- defs if Syntax.math.contains(name) && f.body.isEmpty
    do
      pure += name
      val formals = f.params.map((t, x) => state.exprs.formal(x, typ(t)))
      state = state.declare(name, Nil, formals, typ(f.typ), freely)

    for (name, Function(ret, _, params, _)) <- defs if !pure.contains(name)
    do
      val in = params.map((t, x) => if globals.contains(x) then state.exprs.formal(x, typ(t)).fresh else state.exprs.formal(x, typ(t)))
      val out = if ret == VoidType then Nil else List(state.exprs.formal("result", typ(ret)))
      val scope = globals.toMap ++ (for ((t, x), v) <- params zip in yield x -> (v, t))
      for xs <- assigned(scope, contracts.getOrElse(name, Nil), "assigns")
      do assigns(name) = if name == "main" then (xs ++ initialized.map(globals(_)._1)).distinct.sortBy(_.name.toString) else xs
      val requires = if name == "main" && zeros.nonEmpty then List("requires" -> Some(zeros_)) else Nil
      val contract = clauses(scope, Env(out.headOption.map((_, ret)), None), contracts.getOrElse(name, Nil))
      // the ranges of the parameters of unsigned types of functions with annotations, as in Frama-C/WP
      val ranges =
        if !contracts.contains(name) && !defs(name).body.exists(acsl)
        then Nil
        else
          for ((t, _), v) <- params zip in if t.isInstanceOf[IntType] && !t.asInstanceOf[IntType].signed; phi <- bounds(t, v)
          yield "requires" -> Some(state.exprs.check(core.Scope.empty ++ in, phi, state.types.sort("Bool")))
      val attrs = Attrs(requires ++ ranges ++ contract)

      Error.report("parameter named result", name):
        require(ret == VoidType || !params.exists(_._2 == "result"))

      state = state.declare(name, Nil, in, out, attrs)

    // the bodies in the order of the input, resolved before their modifies clauses are known, which the type check
    // needs (see Call)
    val bodies =
      for case f @ Function(_, name, _, Some(body)) <- tops if defs(name) eq f
      yield name -> define(f, body, if name == "main" then inits.toList else Nil)

    for (name, mod) <- modifies(assigns.toMap, bodies.toMap)
    do state = state.copy(procattrs = state.procattrs.updated(name, Attrs(List("modifies" -> Some(mod))) ++ state.procattrs(name)))

    // the commands in the order of the input, where a function is emitted at its definition
    for top <- tops
    do
      top match
        case Global(Decl(_, _, decls)) =>
          for Declarator(_, x, _, _) <- decls
          do cmds += state.cmds.declareVar(x)

        case _: LogicFun | _: Property =>
          cmds ++= logical.dequeue()

        case f @ Function(_, name, _, _) if defs(name) eq f =>
          f.body match
            case None if pure.contains(name) =>
              cmds += state.cmds.declareFun(name, f.params.length)

            case None =>
              cmds += state.cmds.declareProc(name)

            case Some(_) =>
              state = state.define(name, check(name, bodies.toMap.apply(name)))
              cmds += state.cmds.defineProc(name)

        case _ =>

    // the declarations of floating point numbers, if used (see floats)
    val floatCmds =
      if !floating then Nil
      else List("Float", "Double").map(s => state.cmds.declareSort(s)) ++ Syntax.floats.map((name, args, _) => state.cmds.declareFun(name, args.length))
    floatCmds ++ cmds.toList

  // the modifies clauses of the functions: those of `assigns`, and for the others the global variables that their
  // `bodies` assign, directly or by the functions that they call, as a fixpoint, since they may call each other;
  // functions without body and assigns clause modify none; the calls of the bodies are not resolved yet, they modify
  // no global variables (see Call), and .mod has the assigned local variables and results as well
  def modifies(assigns: Map[String, List[core.Var]], bodies: Map[String, core.Prog]): Map[String, List[core.Var]] =
    val vars = globals.values.map(_._1).toSet
    val direct =
      for (name, body) <- bodies if !assigns.contains(name)
      yield name -> (body.mod intersect vars)

    var mod = direct
    var changed = true
    while changed do
      val mod_ =
        for (name, xs) <- mod
        yield name -> (xs ++ bodies(name).calls.flatMap(g => assigns.get(g.name).map(_.toSet).orElse(mod.get(g.name)).getOrElse(Set())))
      changed = mod_ != mod
      mod = mod_

    val inferred =
      for (name, xs) <- mod if xs.nonEmpty
      yield name -> xs.toList.sortBy(_.name.toString)
    assigns.filter(_._2.nonEmpty) ++ inferred

  // the body of function `name`, checked with its modifies clause, which the inputs and the global variables that it
  // does not modify must not be assigned
  def check(name: String, prog: core.Prog): core.Prog =
    val core.Proc(_, _, in, out) = state.procs(name)
    val mod = state.procattrs(name).modifies.toSet
    val fixed = in.toSet ++ (globals.values.map(_._1).toSet -- mod)
    val scope = core.Scope.empty ++ globals.values.map(_._1).toList ++ in ++ out
    state.progs.check(scope, fixed, mod, prog)

  // the body of `f`, not checked yet (see check): parameters that are assigned are copied into fresh locals, since the
  // inputs of procedures are fixed, followed by the statements on entry, i.e. the initializers of the global variables
  // for main
  def define(f: Function, body: Block, entry: List[core.Prog]): core.Prog =
    val Function(ret, name, params, _) = f
    val core.Proc(_, _, in, out) = state.procs(name)

    val ctx = Ctx(out.headOption.map((_, ret)), mutable.ListBuffer(), labels(body), ends(body), function = name)
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
    state.progs.block(copies.map(_._3) ++ ctx.temps.toList, init ++ entry :+ body_)
