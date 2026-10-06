package cuvee.c

import scala.collection.mutable

import util.Name
import cuvee.Error
import cuvee.core
import cuvee.core.{State, Attrs, Sort, Spec, True, False, Zero, One}
import cuvee.core.{Plus, Minus, Times, UMinus, DivBy, Mod, Lt, Le, Gt, Ge, Eq, Not, And, Or, Ite, Select, Store}

// resolution of a C translation unit into core procedures:
// integer types are Int (unbounded), _Bool is Bool, arrays are values of type Array Int T;
// functions are procedures whose result is the output `result`,
// and whose global variables modified, directly or by calls, are inferred;
// calls inside expressions are evaluated before the statement that contains them, in order
class Parser(var state: State):
  // the signatures of the functions by name
  val functions = mutable.Map[String, Function]()

  // the global variables with their C types
  val globals = mutable.Map[String, (core.Var, Type)]()

  // the context of a function body: its result, and the temporary variables for the results of calls
  case class Ctx(result: Option[(core.Var, Type)], temps: mutable.ListBuffer[core.Var])

  type Scope = Map[String, (core.Var, Type)]

  def typ(t: Type): core.Type =
    t match
      case IntType      => Sort.int
      case BoolType     => Sort.bool
      case ArrayType(e) => Sort.array(Sort.int, typ(e))
      case VoidType     => Error.raise("void is not a type of values")
      case PointerType(_) => Error.raise("pointers are not supported", t)
      case FloatType    => Error.raise("floating point numbers are not supported", t)

  // the value of global variables without initializer, where arrays are constant
  def zero(t: Type): core.Expr =
    t match
      case IntType      => Zero.int
      case BoolType     => False
      case ArrayType(e) => core.App(core.Fun.const, List(typ(e)), typ(t), List(zero(e)))
      case VoidType     => Error.raise("void is not a type of values")
      case PointerType(_) => Error.raise("pointers are not supported", t)
      case FloatType    => Error.raise("floating point numbers are not supported", t)

  def temp(ctx: Ctx, t: Type): core.Var =
    val x = core.Var("tmp", typ(t)).fresh
    ctx.temps += x
    x

  // conversions between integers and truth values as in C
  def toInt(expr: core.Expr, t: Type): core.Expr =
    t match
      case IntType  => expr
      case BoolType => Ite(expr, One.int, Zero.int)
      case _        => Error.raise("not an integer", expr)

  def toBool(expr: core.Expr, t: Type): core.Expr =
    t match
      case BoolType => expr
      case IntType  => Not(Eq(expr, Zero.int))
      case _        => Error.raise("not a truth value", expr)

  def arith(op: String, a: core.Expr, b: core.Expr): core.Expr =
    op match
      case "+" => Plus.int(a, b)
      case "-" => Minus.int(a, b)
      case "*" => Times.int(a, b)
      // division and remainder truncate towards zero in C, unlike div and mod in SMT-LIB (see TODO.md)
      case "/" => DivBy.int(a, b)
      case "%" => Mod.int(a, b)
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
        (Nil, core.Lit(literal(text), Sort.int), IntType)

      case Id("true") if !scope.contains("true") =>
        (Nil, True, BoolType)

      case Id("false") if !scope.contains("false") =>
        (Nil, False, BoolType)

      case Id(x) =>
        Error.report("unknown variable", x):
          require(scope.contains(x))
        val (v, t) = scope(x)
        (Nil, v, t)

      case Index(base, index) =>
        val (pre1, base_, t) = expr(scope, ctx, base)
        val (pre2, index_) = int(scope, ctx, index)
        t match
          case ArrayType(elem) => (pre1 ++ pre2, Select(base_, index_), elem)
          case _               => Error.raise("indexing of an expression that is not an array", base)

      case Call(f, Nil) if f.startsWith("__VERIFIER_nondet_") =>
        val t = if f == "__VERIFIER_nondet_bool" then BoolType else IntType
        val x = temp(ctx, t)
        (List(Spec.havoc(List(x))), x, t)

      case Call(f, args) =>
        val (pre, args_) = arguments(scope, ctx, f, args)
        val ret = functions(f).typ

        Error.report("call of a void function inside an expression", f):
          require(ret != VoidType)

        val x = temp(ctx, ret)
        (pre :+ core.Call(f, args_, List(x)), x, ret)

      case App("-", List(arg)) =>
        val (pre, arg_) = int(scope, ctx, arg)
        (pre, UMinus.int(arg_), IntType)

      case App("!", List(arg)) =>
        val (pre, arg_) = cond(scope, ctx, arg)
        (pre, Not(arg_), BoolType)

      case App(op @ ("&&" | "||"), List(left, right)) =>
        val (pre1, left_) = cond(scope, ctx, left)
        val (pre2, right_) = cond(scope, ctx, right)

        Error.report("calls in the right operand of && and || are not supported", right):
          require(pre2.isEmpty)

        val phi = if op == "&&" then And(left_, right_) else Or(left_, right_)
        (pre1, phi, BoolType)

      case App(op @ ("==" | "!="), List(left, right)) =>
        val (pre1, left_, lt) = expr(scope, ctx, left)
        val (pre2, right_, rt) = expr(scope, ctx, right)

        val eq = (lt, rt) match
          case (BoolType, BoolType)                 => Eq(left_, right_)
          case (ArrayType(_), _) | (_, ArrayType(_)) => Eq(left_, right_)
          case _                                    => Eq(toInt(left_, lt), toInt(right_, rt))

        (pre1 ++ pre2, if op == "==" then eq else Not(eq), BoolType)

      case App(op @ ("<" | "<=" | ">" | ">="), List(left, right)) =>
        val (pre1, left_) = int(scope, ctx, left)
        val (pre2, right_) = int(scope, ctx, right)

        val phi = op match
          case "<"  => Lt.int(left_, right_)
          case "<=" => Le.int(left_, right_)
          case ">"  => Gt.int(left_, right_)
          case _    => Ge.int(left_, right_)

        (pre1 ++ pre2, phi, BoolType)

      case App(op, List(left, right)) =>
        val (pre1, left_) = int(scope, ctx, left)
        val (pre2, right_) = int(scope, ctx, right)
        (pre1 ++ pre2, arith(op, left_, right_), IntType)

      case Cond(e, None) =>
        expr(scope, ctx, e)

      case Cond(test, Some((left, right))) =>
        val (pre0, test_) = cond(scope, ctx, test)
        val (pre1, left_, lt) = expr(scope, ctx, left)
        val (pre2, right_, rt) = expr(scope, ctx, right)

        Error.report("calls in the branches of ?: are not supported", left, right):
          require(pre1.isEmpty && pre2.isEmpty)

        if lt == BoolType && rt == BoolType
        then (pre0, Ite(test_, left_, right_), BoolType)
        else (pre0, Ite(test_, toInt(left_, lt), toInt(right_, rt)), IntType)

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
      case IntType  => int(scope, ctx, e)
      case BoolType => cond(scope, ctx, e)
      case _ =>
        val (pre, e_, t_) = expr(scope, ctx, e)
        Error.report("type mismatch", e, t, t_):
          require(t == t_)
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

  // the statements of a block, whose declarations are the local variables of the core block,
  // which are renamed if they shadow variables in scope
  def block(scope: Scope, ctx: Ctx, stmts: List[Stmt]): core.Prog =
    val locals = mutable.ListBuffer[core.Var]()
    var scope_ = scope

    val progs =
      for stmt <- stmts
      yield stmt match
        case Decl(t, decls) =>
          for
            Declarator(x, size, init) <- decls
            prog <-
              val t_ = if size.isDefined then ArrayType(t) else t
              val v = core.Var(x, typ(t_))
              val v_ = if scope_.values.exists(_._1.name == v.name) then v.fresh else v
              locals += v_
              scope_ = scope_ + (x -> (v_, t_))
              init.toList.flatMap(assign(scope_, ctx, Id(x), "=", _))
          yield prog

        case _ =>
          this.stmt(scope_, ctx, stmt)

    core.Block(locals.toList, progs.flatten)

  def wrap(progs: List[core.Prog]): core.Prog =
    progs match
      case List(prog) => prog
      case _          => core.Block(Nil, progs)

  def stmt(scope: Scope, ctx: Ctx, s: Stmt): List[core.Prog] =
    s match
      case Empty =>
        Nil

      case Break =>
        List(core.Break)

      case Continue =>
        List(core.Continue)

      case _: Decl =>
        List(block(scope, ctx, List(s)))

      case Block(stmts) =>
        List(block(scope, ctx, stmts))

      case Labeled(_, stmt) =>
        this.stmt(scope, ctx, stmt)

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
        pre :+ Spec.assert(phi_)

      case ExprStmt(Call("__VERIFIER_assume", List(phi))) =>
        val (pre, phi_) = cond(scope, ctx, phi)
        pre :+ Spec.assume(phi_)

      case ExprStmt(Call("reach_error" | "__VERIFIER_error", Nil)) =>
        List(Spec.assert(False))

      case ExprStmt(Call("abort", Nil)) =>
        List(Spec.assume(False))

      // calls as statements, whose result is discarded
      case ExprStmt(Call(f, args)) if functions.contains(f) =>
        val (pre, args_) = arguments(scope, ctx, f, args)
        val ret = functions(f).typ
        val res = if ret == VoidType then Nil else List(temp(ctx, ret))
        pre :+ core.Call(f, args_, res)

      case ExprStmt(e) =>
        val (pre, _, _) = expr(scope, ctx, e)
        pre

      case If(test, left, right) =>
        val (pre, test_) = cond(scope, ctx, test)
        val left_ = wrap(stmt(scope, ctx, left))
        val right_ = wrap(right.toList.flatMap(stmt(scope, ctx, _)))
        pre :+ core.If(test_, left_, right_)

      case While(test, body) =>
        val (pre, test_) = cond(scope, ctx, test)

        Error.report("calls in loop conditions are not supported", test):
          require(pre.isEmpty)

        List(while_(test_, wrap(stmt(scope, ctx, body))))

      // the test is evaluated after each iteration, also after continue, but not before the first one
      case DoWhile(body, test) =>
        val (pre, test_) = cond(scope, ctx, test)

        Error.report("calls in loop conditions are not supported", test):
          require(pre.isEmpty)

        val first = temp(ctx, BoolType)
        val body_ = core.Block(Nil, core.Assign(List(first), List(False)) :: stmt(scope, ctx, body))
        List(core.Assign(List(first), List(True)), while_(Or(first, test_), body_))

      // the initialization may declare variables, whose scope is the loop
      case For(init, test, step, body) =>
        List(block(scope, ctx, init.toList :+ Loop(test, body, step)))

      // continue must execute the step: the body is an inner loop that is left by break instead of continue,
      // and a break of the body sets a flag that leaves the outer loop
      case Loop(test, body, step) =>
        val (pre, test_) = test.map(cond(scope, ctx, _)).getOrElse((Nil, True))

        Error.report("calls in loop conditions are not supported", test):
          require(pre.isEmpty)

        val body_ = stmt(scope, ctx, body)
        val step_ = step.toList.flatMap(stmt(scope, ctx, _))

        if !body_.exists(continues)
        then List(while_(test_, core.Block(Nil, body_ ++ step_)))
        else
          val brk = temp(ctx, BoolType)
          val inner = while_(True, core.Block(Nil, body_.map(exits(brk, _)) :+ core.Break))
          val leave = core.If(brk, core.Break, core.Block(Nil, Nil))
          val outer = while_(test_, core.Block(Nil, List(inner, leave) ++ step_))
          List(core.Assign(List(brk), List(False)), outer)

      case Return(None) =>
        Error.report("return without value from a function with result"):
          require(ctx.result.isEmpty)
        List(core.Return)

      case Return(Some(e)) =>
        Error.report("return with value from a void function", e):
          require(ctx.result.isDefined)

        val Some((result, t)) = ctx.result: @unchecked
        val (pre, e_) = value(scope, ctx, e, t)
        pre ++ List(core.Assign(List(result), List(e_)), core.Return)

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
      case core.Continue            => core.Break
      case core.Break               => core.Block(Nil, List(core.Assign(List(brk), List(True)), core.Break))
      case core.Block(locals, progs) => core.Block(locals, progs.map(exits(brk, _)))
      case core.If(test, left, right) => core.If(test, exits(brk, left), exits(brk, right))
      case core.Choice(progs)       => core.Choice(progs.map(exits(brk, _)))
      case _                        => prog

  // assignments x op= e and a[i] op= e, where arrays are values that are updated as a whole
  // the arithmetic operators of compound assignments x += e and of increments x++ and decrements x--,
  // which are x = x + e, x = x + 1, and x = x - 1
  val compound = Map("+=" -> "+", "-=" -> "-", "*=" -> "*", "/=" -> "/", "%=" -> "%", "++" -> "+", "--" -> "-")

  def assign(scope: Scope, ctx: Ctx, lhs: Expr, op: String, rhs: Expr): List[core.Prog] =
    lhs match
      // nondeterministic values and results of calls are assigned directly, without temporary variables
      case Id(x) if op == "=" && scope.contains(x) && nondet(rhs, scope(x)._2) =>
        List(Spec.havoc(List(scope(x)._1)))

      case Id(x) if op == "=" && scope.contains(x) && direct(rhs, scope(x)._2) =>
        val Call(f, args) = rhs: @unchecked
        val (pre, args_) = arguments(scope, ctx, f, args)
        pre :+ core.Call(f, args_, List(scope(x)._1))

      case Id(x) =>
        Error.report("unknown variable", x):
          require(scope.contains(x))

        val (v, t) = scope(x)
        val (pre, rhs_) =
          if op == "="
          then value(scope, ctx, rhs, t)
          else
            val (pre, rhs_) = int(scope, ctx, rhs)
            (pre, arith(op, toInt(v, t), rhs_))

        pre :+ core.Assign(List(v), List(rhs_))

      case Index(Id(a), index) =>
        Error.report("unknown variable", a):
          require(scope.contains(a))

        val (v, t) = scope(a)
        val elem = t match
          case ArrayType(elem) => elem
          case _               => Error.raise("indexing of a variable that is not an array", a)

        val (pre1, index_) = int(scope, ctx, index)
        val (pre2, rhs_) =
          if op == "="
          then value(scope, ctx, rhs, elem)
          else
            val (pre, rhs_) = int(scope, ctx, rhs)
            (pre, arith(op, toInt(Select(v, index_), elem), rhs_))

        pre1 ++ pre2 :+ core.Assign(List(v), List(Store(v, index_, rhs_)))

      case _ =>
        Error.raise("invalid left hand side of assignment", lhs)

  def nondet(rhs: Expr, t: Type) =
    rhs match
      case Call("__VERIFIER_nondet_bool", Nil) => t == BoolType
      case Call(f, Nil)                        => f.startsWith("__VERIFIER_nondet_") && t == IntType
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
    core.While(test, body, attrs)

  // calls of functions whose result has the type of the variable, which needs no conversion
  def direct(rhs: Expr, t: Type) =
    rhs match
      case Call(f, _) => functions.get(f).exists(_.typ == t)
      case _          => false

  // the names assigned in a statement, syntactically, for the parameters that must be copied into locals
  def assigned(s: Stmt): Set[String] =
    s match
      case Assign(Id(x), _, _)           => Set(x)
      case Assign(Index(Id(x), _), _, _) => Set(x)
      case If(_, left, right)            => assigned(left) ++ right.toSet.flatMap(assigned)
      case While(_, body)                => assigned(body)
      case DoWhile(body, _)              => assigned(body)
      case For(init, _, step, body)      => init.toSet.flatMap(assigned) ++ step.toSet.flatMap(assigned) ++ assigned(body)
      case Loop(_, body, step)           => step.toSet.flatMap(assigned) ++ assigned(body)
      case Block(stmts)                  => stmts.toSet.flatMap(assigned)
      case Labeled(_, stmt)              => assigned(stmt)
      case _                             => Set()

  // the global variables assigned in a function body directly, respecting local declarations that shadow them,
  // and the functions that it calls
  def effects(scope: Set[String], s: Stmt): (Set[String], Set[String]) =
    def calls(e: Expr): Set[String] =
      e match
        case Call(f, args)        => args.toSet.flatMap(calls) + f
        case Index(base, index)   => calls(base) ++ calls(index)
        case App(_, args)         => args.toSet.flatMap(calls)
        case Cond(test, branches) => calls(test) ++ branches.toSet.flatMap((left, right) => calls(left) ++ calls(right))
        case _                    => Set()

    def global(x: String) =
      if globals.contains(x) && !scope.contains(x) then Set(x) else Set()

    def all(scope: Set[String], stmts: List[Stmt]): (Set[String], Set[String]) =
      stmts match
        case Nil =>
          (Set(), Set())

        case Decl(_, decls) :: rest =>
          val inits = decls.flatMap(_.init).toSet.flatMap(calls)
          val (mod, called) = all(scope ++ decls.map(_.name), rest)
          (mod, called ++ inits)

        case stmt :: rest =>
          val (mod1, called1) = effects(scope, stmt)
          val (mod2, called2) = all(scope, rest)
          (mod1 ++ mod2, called1 ++ called2)

    s match
      case Assign(Id(x), _, rhs)               => (global(x), calls(rhs))
      case Assign(Index(Id(x), i), _, rhs)     => (global(x), calls(i) ++ calls(rhs))
      case ExprStmt(e)                         => (Set(), calls(e))
      case Return(e)                           => (Set(), e.toSet.flatMap(calls))
      case If(test, left, right)               => all(scope, List(ExprStmt(test), left) ++ right.toList)
      case While(test, body)                   => all(scope, List(ExprStmt(test), body))
      case DoWhile(body, test)                 => all(scope, List(body, ExprStmt(test)))
      case For(init, test, step, body)         => all(scope, init.toList ++ test.map(ExprStmt(_)).toList ++ step.toList :+ body)
      case Loop(test, body, step)              => all(scope, test.map(ExprStmt(_)).toList ++ step.toList :+ body)
      case Block(stmts)                        => all(scope, stmts)
      case Labeled(_, stmt)                    => all(scope, List(stmt))
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
    val tops = unit.filter:
      case Function(_, name, _, _) => !Syntax.builtin(name)
      case _                       => true

    // the signatures of all functions are known before any body is resolved
    for case f @ Function(_, name, _, _) <- tops if !functions.contains(name)
    do functions(name) = f

    // the definition of each function, otherwise its last declaration
    val defs =
      for (name, group) <- tops.collect { case f: Function => f }.groupBy(_.name)
      yield name -> group.find(_.body.isDefined).getOrElse(group.last)

    val cmds = mutable.ListBuffer[core.Cmd]()

    // the initial values of the global variables, which may refer to those declared before,
    // are the precondition of main, the entry point of the program;
    // global variables without initializer are zero, as in C
    val inits = mutable.ListBuffer[core.Expr]()

    for case Global(Decl(t, decls)) <- tops; Declarator(x, size, init) <- decls
    do
      val t_ = if size.isDefined then ArrayType(t) else t

      for e <- init
      do
        Error.report("initialized global array", x):
          require(size.isEmpty)

        val (progs, e_) = value(globals.toMap, Ctx(None, mutable.ListBuffer()), e, t_)
        Error.report("initial value of global variable must not call functions", x, e):
          require(progs.isEmpty)

        inits += Eq(core.Var(x, typ(t_)), e_)

      if init.isEmpty
      then inits += Eq(core.Var(x, typ(t_)), zero(t_))

      state = state.declare(x, typ(t_), Attrs.empty)
      globals(x) = (state.vars(x), t_)

    val mod = modifies(defs.values.toList)

    // procedures are declared before the bodies are resolved, since they may call each other
    for (name, Function(ret, _, params, _)) <- defs
    do
      val in = params.map((t, x) => core.Var(x, typ(t)))
      val out = if ret == VoidType then Nil else List(core.Var("result", typ(ret)))
      val mod_ = mod(name).toList.sorted.map(globals(_)._1)
      val modifies = if mod_.isEmpty then Nil else List("modifies" -> Some(mod_))
      val requires = if name == "main" && inits.nonEmpty then List("requires" -> Some(And(inits.toList))) else Nil
      val attrs = Attrs(modifies ++ requires)

      Error.report("parameter named result", name):
        require(ret == VoidType || !params.exists(_._2 == "result"))

      state = state.declare(name, Nil, in, out, attrs)

    // the commands in the order of the input, where a function is emitted at its definition
    for top <- tops
    do
      top match
        case Global(Decl(_, decls)) =>
          for Declarator(x, _, _) <- decls
          do cmds += state.cmds.declareVar(x)

        case f @ Function(_, name, _, _) if defs(name) eq f =>
          f.body match
            case None =>
              cmds += state.cmds.declareProc(name)

            case Some(body) =>
              val body_ = define(f, body, mod(name))
              state = state.define(name, body_)
              cmds += state.cmds.defineProc(name)

        case _ =>

    cmds.toList

  // parameters that are assigned are copied into fresh locals, since the inputs of procedures are fixed
  def define(f: Function, body: Block, mod: Set[String]): core.Prog =
    val Function(ret, name, params, _) = f
    val core.Proc(_, _, in, out) = state.procs(name)

    val ctx = Ctx(out.headOption.map((_, ret)), mutable.ListBuffer())
    val written = assigned(body)

    val copies =
      for ((t, x), v) <- params zip in if written.contains(x)
      yield (x, v, v.fresh, t)

    val scope =
      globals.toMap ++
        (for ((t, x), v) <- params zip in yield x -> (v, t)) ++
        (for (x, _, copy, t) <- copies yield x -> (copy, t))

    val body_ = block(scope, ctx, body.stmts)
    val init = for (_, v, copy, _) <- copies yield core.Assign(List(copy), List(v))
    val prog = core.Block(copies.map(_._3) ++ ctx.temps.toList, init :+ body_)

    val fixed = in.toSet ++ (globals.values.map(_._1).toSet -- mod.map(globals(_)._1))
    val scope_ = core.Scope.empty ++ globals.values.map(_._1).toList ++ in ++ out
    state.progs.check(scope_, fixed, mod.map(globals(_)._1), prog)
