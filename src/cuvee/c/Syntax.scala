package cuvee.c

import easyparse.Token

import cuvee.Error

object Syntax:
  def apply(name: String) =
    Token.Keyword(name)

  def apply(name: String, text: String) =
    Token.Value(name, text)

  def error(msg: String) =
    Error.raise(msg)

  // the functions of the verification conventions of SV-COMP and of assert.h, which are not procedures,
  // hence their bodies are skipped by the grammar and their declarations are dropped by the parser
  def builtin(name: String) =
    name == "assert" || name == "reach_error" || name == "abort" || name.startsWith("__assert") || name.startsWith("__VERIFIER_")

sealed trait Type
case object IntType extends Type
case object BoolType extends Type
case object VoidType extends Type
case class ArrayType(elem: Type) extends Type
// pointers and floating point numbers only in the signatures of builtins, the parser rejects them otherwise
case class PointerType(elem: Type) extends Type
case object FloatType extends Type

sealed trait Expr
case class Num(value: String) extends Expr
case class Id(name: String) extends Expr
case class Index(base: Expr, index: Expr) extends Expr
case class Call(fun: String, args: List[Expr]) extends Expr
case class App(op: String, args: List[Expr]) extends Expr
case class Cond(test: Expr, branches: Option[(Expr, Expr)]) extends Expr

object Num extends (String => Expr)
object Id extends (String => Expr)
object Call extends ((String, List[Expr]) => Expr)
object App extends ((String, List[Expr]) => Expr)
object Cond extends ((Expr, Option[(Expr, Expr)]) => Expr)

case class Declarator(name: String, size: Option[Option[Expr]], init: Option[Expr])
object Declarator extends ((String, Option[Option[Expr]], Option[Expr]) => Declarator)

sealed trait Stmt
case class Decl(typ: Type, decls: List[Declarator]) extends Stmt
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
// labels are dropped, as there is no goto
case class Labeled(label: String, stmt: Stmt) extends Stmt

object Decl extends ((Type, List[Declarator]) => Decl)
object Assign extends ((Expr, String, Expr) => Stmt)
object ExprStmt extends (Expr => Stmt)
object If extends ((Expr, Stmt, Option[Stmt]) => Stmt)
object While extends ((Expr, Stmt) => Stmt)
object DoWhile extends ((Stmt, Expr) => Stmt)
object For extends ((Option[Stmt], Option[Expr], Option[Stmt], Stmt) => Stmt)
object Return extends (Option[Expr] => Stmt)
object Block extends (List[Stmt] => Block)
object Labeled extends ((String, Stmt) => Stmt)

sealed trait Top
case class Global(decl: Decl) extends Top
case class Function(typ: Type, name: String, params: List[(Type, String)], body: Option[Block]) extends Top

object Global extends (Decl => Top)
object Function extends ((Type, String, List[(Type, String)], Option[Block]) => Top)

case class Loop(test: Option[Expr], body: Stmt, step: Option[Stmt]) extends Stmt
