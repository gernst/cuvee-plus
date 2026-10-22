package cuvee.transform

import util.Name
import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._

// flattening of records, i.e., datatypes with a single constructor that are not recursive:
// their declarations are dropped, values of records are replaced by the fields, recursively for nested records,
// in the formal parameters of functions, where functions whose result is a record are split into one per field,
// named after the function and the selectors, and in bound variables, which are replaced by the constructor
// applied to fresh variables for the fields; terms of records are constructors, selectors, ite, and applications
// of such functions, equations between them become conjunctions of equations between their fields,
// selectors and testers are reduced; let, match, and as on records are not supported,
// neither are type parameters that are instantiated by records, e.g. in arrays of records;
// in clauses ∀ xs. φ₁ ∧ ... ∧ φₙ ⇒ ψ, equations x == t of the antecedent with x among xs are inlined (see eliminate)
object Flat extends Transform:
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Option[Cmd]): (List[Cmd], Option[Cmd]) =
    val cmds_ =
      for
        cmd <- cmds
        cmd_ <- flat(state, cmd)
      yield cmd_

    (cmds_, last)

  def flat(state: State, cmd: Cmd): List[Cmd] =
    cmd match
      // other datatypes of the same group are kept
      case DeclareDatatypes(cons, datas, attrs) =>
        val (cons_, datas_) = (cons zip datas).filterNot((con, _) => isRecord(state, con)).unzip
        if cons_.isEmpty
        then Nil
        else List(DeclareDatatypes(cons_, datas_, attrs))

      case DeclareFun(fun, attrs) if isFlattened(state, fun) =>
        for fun_ <- functions(state, fun)
        yield DeclareFun(fun_, attrs)

      // the formal parameters are replaced by the constructors applied to their fields, as bound variables
      case DefineFun(fun, body, attrs) if isFlattened(state, fun) =>
        val (_, body_) = bind(state, Type.expand(state, fun.formals), body)
        for (fun_, body__) <- functions(state, fun) zip leaf(state, body_)
        yield DefineFun(fun_, body__, attrs)

      case DefineFun(fun, body, attrs) =>
        List(DefineFun(fun, flat(state, body), attrs))

      case Assert(justify, params, phi, attrs) =>
        List(Assert(justify, params, eliminate(flat(state, phi)), attrs))

      case _ =>
        List(cmd)

  // the sort constructor `con` is a record
  def isRecord(state: State, con: Con): Boolean =
    datatype(state, Sort(con, Nil)).isDefined

  // the datatype of `typ` if it has a single constructor and is not recursive, i.e., it is a record,
  // together with `typ` as an instance of the datatype
  def datatype(state: State, typ: Type): Option[(Sort, Datatype, Fun)] =
    typ match
      case sort @ Sort(con, _) if state.datatypes.contains(con.name) && !recursive(state, con) =>
        state.datatypes(con.name) match
          case data @ Datatype(_, List((constr, _))) =>
            Some((sort, data, constr))

          case _ =>
            None

      case _ =>
        None

  // the sort `con` occurs in the fields of its datatype, possibly through other datatypes
  def recursive(state: State, con: Con): Boolean =
    // the types of the fields of all constructors of a datatype
    def fields(con: Con): List[Type] =
      state.datatypes.get(con.name) match
        case Some(data) => data.sels.map(_.res)
        case None       => Nil

    // the sorts reachable from `cons` through the fields of datatypes
    def reachable(cons: Set[Con], seen: Set[Con]): Set[Con] =
      val next = cons -- seen
      if next.isEmpty
      then seen
      else reachable(next.flatMap(fields(_).cons), seen ++ next)

    reachable(fields(con).cons, Set()).contains(con)

  // the types of the fields of `constr` in the instance `typ` of the datatype,
  // where the parameters are instantiated by the arguments of `typ`
  def fields(data: Datatype, typ: Sort, constr: Fun): List[Type] =
    val su = Subst.from(data.params, typ.args)
    val Some((_, sels)) = data.constrs.find(_._1 == constr): @unchecked
    sels.map(sel => su(sel.res))

  // the constructor applied to values for its fields, a value of the instance `typ` of the datatype
  def construct(data: Datatype, typ: Sort, constr: Fun, args: List[Expr]): Expr =
    App(constr, fields(data, typ, constr), typ, args)

  // the selector applied to a value of the instance `typ` of the datatype
  def select(data: Datatype, typ: Sort, sel: Fun, arg: Expr): Expr =
    val su = Subst.from(data.params, typ.args)
    App(sel, List(typ), su(sel.res), List(arg))

  // whether values of `typ` are records, whose fields replace them
  def isDatatype(state: State, typ: Type) =
    datatype(state, typ).isDefined

  // functions whose signature contains records, except for the constructors and selectors of datatypes
  def isFlattened(state: State, fun: Fun): Boolean =
    (fun.args :+ fun.res).exists(isDatatype(state, _))
      && !state.datatypes.values.exists(data => data.constrs.exists((constr, sels) => constr == fun || sels.contains(fun)))

  // the functions that replace `fun`, whose formal parameters are the fields of the original ones,
  // one for each field of the result, named after the function and the selectors, or `fun` with these parameters
  def functions(state: State, fun: Fun): List[Fun] =
    val Fun(name, params, formals, res) = fun
    val formals_ = formals.flatMap(leaves(state, _))
    for leaf <- leaves(state, Var(name, res))
    yield Fun(leaf.name, params, formals_, leaf.typ)

  // the number of fields of `typ`, recursively for nested records, 1 for other types
  def width(state: State, typ: Type): Int =
    leaves(state, Var("_", typ)).length

  // the variables for the fields of `x`, named x_sel, recursively for nested records
  def leaves(state: State, x: Var): List[Var] =
    datatype(state, x.typ) match
      case None =>
        List(x)

      case Some((sort, data, constr)) =>
        for
          (sel, typ) <- data.sels zip fields(data, sort, constr);
          leaf <- leaves(state, Var(Name(x.name.name + "_" + sel.name.name, x.name.index), typ))
        yield leaf

  // a value of type `typ` in terms of the variables for its fields, together with the unused variables
  def build(state: State, typ: Type, leaves: List[Var]): (Expr, List[Var]) =
    datatype(state, typ) match
      case None =>
        (leaves.head, leaves.tail)

      case Some((sort, data, constr)) =>
        val (args, rest) =
          fields(data, sort, constr).foldLeft((List.empty[Expr], leaves)):
            case ((args, leaves), typ) =>
              val (arg, rest) = build(state, typ, leaves)
              (args :+ arg, rest)

        (construct(data, sort, constr, args), rest)

  // the fields of `expr` if it is a record, otherwise `expr` itself, flattened
  def leaf(state: State, expr: Expr): List[Expr] =
    if isDatatype(state, expr.typ)
    then parts(state, expr)
    else List(flat(state, expr))

  // the fields of a term of a record, recursively for nested records
  def parts(state: State, expr: Expr): List[Expr] =
    val Some((_, _, constr)) = datatype(state, expr.typ): @unchecked

    expr match
      case App(`constr`, _, _, args) =>
        args.flatMap(leaf(state, _))

      case App(sel, _, _, List(arg)) if isSelector(state, sel, arg) =>
        field(state, sel, arg)

      case Ite(test, left, right) =>
        for (left_, right_) <- parts(state, left) zip parts(state, right)
        yield Ite(flat(state, test), left_, right_)

      case App(fun, _, typ, args) if isFlattened(state, fun) =>
        val args_ = arguments(state, fun, args)
        val leaves_ = leaves(state, Var(fun.name, typ))
        val funs_ = functions(state, fun)

        Error.report("record instantiates a type parameter", fun, typ):
          require(funs_.length == leaves_.length)

        for (fun_, leaf_) <- funs_ zip leaves_
        yield App(fun_, args_.types, leaf_.typ, args_)

      case _ =>
        Error.raise("term of a record not supported", expr)

  // the fields of `arg` selected by `sel`, a single one unless the field is a record itself
  def field(state: State, sel: Fun, arg: Expr): List[Expr] =
    val Some((sort, data, constr)) = datatype(state, arg.typ): @unchecked
    val widths = fields(data, sort, constr).map(width(state, _))
    val k = data.sels.indexOf(sel)
    val from = widths.take(k).sum
    parts(state, arg).slice(from, from + widths(k))

  def isSelector(state: State, sel: Fun, arg: Expr): Boolean =
    datatype(state, arg.typ).exists((_, data, _) => data.sels.contains(sel))

  // the arguments of `fun` with records replaced by their fields, according to the formal parameters,
  // whose number of fields must agree with that of the arguments, which fails for type parameters instantiated by records
  def arguments(state: State, fun: Fun, args: List[Expr]): List[Expr] =
    for
      (x, arg) <- fun.formals zip args
      arg_ <-
        Error.report("record instantiates a type parameter", fun, x, arg):
          require(width(state, x.typ) == width(state, arg.typ))
        leaf(state, arg)
    yield arg_

  // bound variables of the sorts of records are replaced by the constructor applied to fresh variables for the fields,
  // which are fresh if their names clash with the other variables of the binder
  def bind(state: State, bound: List[Var], body: Expr): (List[Var], Expr) =
    val taken = (bound ++ body.free).map(_.name).toSet

    val pairs =
      for x <- bound
      yield
        val leaves_ = leaves(state, x)
        if leaves_ == List(x)
        then (leaves_, None)
        else
          val leaves__ = if leaves_.exists(y => taken.contains(y.name)) then leaves_.fresh else leaves_
          val (expr, _) = build(state, x.typ, leaves__)
          (leaves__, Some(x -> expr))

    val (bound_, substs) = pairs.unzip
    val (xs, exprs) = substs.flatten.unzip
    val su = Subst.from(xs, exprs)
    (bound_.flatten, su(body))

  // the flattened formula or term, which is not a record
  def flat(state: State, expr: Expr): Expr =
    expr match
      case Bind(quant, bound, body) =>
        val (bound_, body_) = bind(state, bound, body)
        Bind(quant, bound_, flat(state, body_))

      case Eq(left, right) if isDatatype(state, left.typ) =>
        And(Eq(parts(state, left), parts(state, right)))

      case Distinct(exprs) if isDatatype(state, exprs.head.typ) =>
        val parts_ = exprs.map(parts(state, _))
        val pairs =
          for
            (left, i) <- parts_.zipWithIndex
            right <- parts_.drop(i + 1)
          yield Not(And(Eq(left, right)))
        And(pairs)

      case Is(arg, fun) if isDatatype(state, arg.typ) =>
        val Some((_, _, constr)) = datatype(state, arg.typ): @unchecked
        if constr == fun then True else False

      case App(sel, _, _, List(arg)) if isSelector(state, sel, arg) =>
        val List(field_) = field(state, sel, arg): @unchecked
        field_

      case App(fun, _, typ, args) if isFlattened(state, fun) =>
        val List(fun_) = functions(state, fun): @unchecked
        val args_ = arguments(state, fun, args)
        App(fun_, args_.types, typ, args_)

      // other functions take records only for their type parameters, e.g. the values of arrays
      case App(fun, _, _, args) if args.exists(arg => isDatatype(state, arg.typ)) =>
        Error.raise("record instantiates a type parameter", fun, expr)

      case _ =>
        expr.map(flat(state, _))

  // the clause ∀ xs. φ₁ ∧ ... ∧ φₙ ⇒ ψ without the equations x == t (or t == x) of the antecedent
  // whose variable x is bound by the clause and does not occur in t, which replace x in the other conjuncts and the head,
  // e.g. those between the fields of records; other formulas are kept
  def eliminate(phi: Expr): Expr =
    phi match
      case All(bound, Imp(ante, head)) =>
        val (phis_, head_) = eliminate(bound.toSet, And.flattenStrong(ante), head)
        val phi_ = Imp(And(phis_), head_)
        All(bound.filter(phi_.free), phi_)

      case _ =>
        phi

  def eliminate(bound: Set[Var], phis: List[Expr], head: Expr): (List[Expr], Expr) =
    val eqs =
      phis.zipWithIndex.collectFirst:
        case (Eq(x: Var, t), i) if bound.contains(x) && !t.free.contains(x) => (x, t, i)
        case (Eq(t, x: Var), i) if bound.contains(x) && !t.free.contains(x) => (x, t, i)

    eqs match
      case Some((x, t, i)) =>
        val su = Subst.from(List(x), List(t))
        eliminate(bound - x, su(phis.patch(i, Nil, 1)), su(head))

      case None =>
        (phis, head)
