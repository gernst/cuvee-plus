package cuvee.c

import easyparse.Token

object Syntax:
  def apply(name: String) =
    Token.Keyword(name)

  def apply(name: String, text: String) =
    Token.Value(name, text)

// integer types, _Bool, void, and arrays of these, which are values unlike in C
sealed trait Type
case object IntType extends Type
case object BoolType extends Type
case object VoidType extends Type
case class ArrayType(elem: Type) extends Type

sealed trait Expr
case class Num(value: String) extends Expr
case class Id(name: String) extends Expr
case class Index(base: Expr, index: Expr) extends Expr
case class Call(fun: String, args: List[Expr]) extends Expr
case class Unary(op: String, arg: Expr) extends Expr
case class Binary(op: String, left: Expr, right: Expr) extends Expr
case class Cond(test: Expr, left: Expr, right: Expr) extends Expr

object Num extends (String => Expr)
object Id extends (String => Expr)
object Call extends ((String, List[Expr]) => Expr)
object Cond extends ((Expr, Expr, Expr) => Expr)

// declarations of variables and arrays, int x = 1, a[10], b[];, whose size is ignored
case class Declarator(name: String, size: Option[Option[Expr]], init: Option[Expr])
object Declarator extends ((String, Option[Option[Expr]], Option[Expr]) => Declarator)

sealed trait Stmt
case class Decl(typ: Type, decls: List[Declarator]) extends Stmt
// assignments x = e, x += e, a[i] = e, and increments x++, as statements only
case class Assign(lhs: Expr, op: String, rhs: Expr) extends Stmt
case class ExprStmt(expr: Expr) extends Stmt
case class If(test: Expr, left: Stmt, right: Option[Stmt]) extends Stmt
case class While(test: Expr, body: Stmt) extends Stmt
case class DoWhile(body: Stmt, test: Expr) extends Stmt
case class For(init: Option[Stmt], test: Option[Expr], step: Option[Stmt], body: Stmt) extends Stmt
case class Return(expr: Option[Expr]) extends Stmt
case class Block(stmts: List[Stmt]) extends Stmt
case object Break extends Stmt
case object Continue extends Stmt
case object Empty extends Stmt

object Decl extends ((Type, List[Declarator]) => Decl)
object Assign extends ((Expr, String, Expr) => Stmt)
object ExprStmt extends (Expr => Stmt)
object If extends ((Expr, Stmt, Option[Stmt]) => Stmt)
object While extends ((Expr, Stmt) => Stmt)
object DoWhile extends ((Stmt, Expr) => Stmt)
object For extends ((Option[Stmt], Option[Expr], Option[Stmt], Stmt) => Stmt)
object Return extends (Option[Expr] => Stmt)
object Block extends (List[Stmt] => Block)

// top-level declarations: global variables, and functions with or without body
sealed trait Top
case class Global(decl: Decl) extends Top
case class Function(typ: Type, name: String, params: List[(Type, String)], body: Option[Block]) extends Top

// internal: the loop of a for statement, whose initialization is resolved separately
case class Loop(test: Option[Expr], body: Stmt, step: Option[Stmt]) extends Stmt
