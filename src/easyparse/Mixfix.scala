package easyparse

case class M[A](
    op: Parser[String],
    prefix_ops: Map[String, Int],
    postfix_ops: Map[String, Int],
    infix_ops: Map[String, (Assoc, Int)],
    min: Int = 0,
    max: Int = Int.MaxValue
)(implicit name: sourcecode.Name):
  infix def $(inner_expr: => Parser[A], apply: (String, List[A]) => A) =
    Mixfix(
      name.value,
      op,
      () => inner_expr,
      apply,
      prefix_ops,
      postfix_ops,
      infix_ops,
      min,
      max
    )

enum Assoc:
  case Non
  case Left
  case Right

case class Mixfix[Expr](
    name: String,
    op: Parser[String],
    inner_expr: () => Parser[Expr],
    apply: (String, List[Expr]) => Expr,
    prefix_ops: Map[String, Int],
    postfix_ops: Map[String, Int],
    infix_ops: Map[String, (Assoc, Int)],
    min: Int,
    max: Int
) extends Parser[Expr]:
  def parse(in: Input, cm: Boolean) =
    mixfix_app(min, in, cm)

  def nprec(assoc: Assoc, prec: Int) =
    if (assoc == Assoc.Left) prec else prec - 1

  def rprec(assoc: Assoc, prec: Int) =
    if (assoc == Assoc.Right) prec else prec + 1

  def check(ok: Boolean, in: Input, cm: Boolean) =
    if (!ok) Input.fail(name, in, cm)

  def operator[A](table: Map[String, A], in: Input, cm: Boolean) =
    val (key, in_) = op.parse(in, cm)
    if table.contains(key)
    then (key, table(key), in_)
    else Input.fail(name, in, cm)

  def unary(op: String, arg: Expr) =
    apply(op, List(arg))

  def binary(op: String, arg1: Expr, arg2: Expr) =
    apply(op, List(arg1, arg2))

  def mixfix_arg(lower: Int, in: Input, cm: Boolean): (Expr, Input) = {
    prefix_app(lower, in, false)
  } or {
    inner_expr().parse(in, cm)
  }

  def prefix_app(lower: Int, in0: Input, cm: Boolean) =
    val (op, prec, in1) = operator(prefix_ops, in0, false)
    check(lower <= prec, in0, cm)
    val (right, in2) = mixfix_app(prec, in1, true)
    (unary(op, right), in2)

  def postfix_app(
      lower: Int,
      upper: Int,
      left: Expr,
      in0: Input,
      cm: Boolean
  ) =
    val (op, prec, in1) = operator(postfix_ops, in0, false)
    check(lower <= prec && prec <= upper, in0, cm)
    postinfix_app(lower, prec, unary(op, left), in1, true)

  def infix_app(
      lower: Int,
      upper: Int,
      left: Expr,
      in0: Input,
      cm: Boolean
  ) =
    val (op, (assoc, prec), in1) = operator(infix_ops, in0, false)
    check(lower <= prec && prec <= upper, in0, cm)
    val (right, in2) = mixfix_app(rprec(assoc, prec), in1, true)
    postinfix_app(lower, nprec(assoc, prec), binary(op, left, right), in2, cm)

  def postinfix_app(
      lower: Int,
      upper: Int,
      left: Expr,
      in: Input,
      cm: Boolean
  ): (Expr, Input) = {
    infix_app(lower, upper, left, in, false)
  } or {
    postfix_app(lower, upper, left, in, false)
  } or {
    (left, in)
  }

  def mixfix_app(lower: Int, in0: Input, cm: Boolean): (Expr, Input) =
    val (left, in1) = mixfix_arg(lower, in0, cm)
    postinfix_app(lower, max, left, in1, true)
