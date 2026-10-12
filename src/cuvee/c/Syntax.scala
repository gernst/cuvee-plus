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
    name == "assert" || name == "reach_error" || name == "abort" || name.startsWith("__assert") || name.startsWith("__VERIFIER_") ||
      allocation(name)

  // the functions of the prelude that compute modulo the range of an unsigned type of 1, 2, 4, or 8 bytes, with the
  // type that a cast to it denotes, e.g. uint(x) as (unsigned int) x (see resources/cuvee/c/prelude.bpl)
  val overflows =
    Map("uchar" -> "unsigned char", "ushort" -> "unsigned short", "uint" -> "unsigned int", "ulonglong" -> "unsigned long long")

  // allocations of arrays (see Parser.allocation), also safe_malloc and safe_calloc, with which SV-COMP replaces
  // allocations that are not checked for NULL, defined in the tasks as abort() on NULL, which the allocations never
  // return here
  def allocation(name: String) =
    name == "malloc" || name == "calloc" || name == "alloca" || name == "free" || name == "safe_malloc" ||
      name == "safe_calloc"

sealed trait Type
// integer types by their signedness and rank, char, short, int, long, or longlong (long long), e.g. unsigned long is
// IntType(false, "long"), where plain char is signed, as on x86 Linux; their sizes follow the data model (see Parser.size)
case class IntType(signed: Boolean, rank: String) extends Type
case object BoolType extends Type
case object VoidType extends Type
case class ArrayType(elem: Type) extends Type
// pointers and floating point numbers only in the signatures of builtins, the parser rejects them otherwise
case class PointerType(elem: Type) extends Type
case object FloatType extends Type
// the mathematical integers of ACSL, integer, the type of its arithmetic
case object Integer extends Type

sealed trait Expr
case class Num(value: String) extends Expr
// floating point constants, e.g. 2.0, which the parser rejects
case class FloatNum(value: String) extends Expr
case class Id(name: String) extends Expr
case class Index(base: Expr, index: Expr) extends Expr
case class Call(fun: String, args: List[Expr]) extends Expr
case class App(op: String, args: List[Expr]) extends Expr
case class Cond(test: Expr, branches: Option[(Expr, Expr)]) extends Expr
case class Cast(typ: Type, expr: Expr) extends Expr
// increments and decrements inside expressions, x++ and x-- (post) or ++x and --x
case class Incr(lhs: Expr, op: String, post: Boolean) extends Expr
// the words of an integer type, e.g. unsigned long, or an expression
case class SizeofType(words: List[String]) extends Expr
case class SizeofExpr(expr: Expr) extends Expr
// initializer lists of arrays, only in declarations
case class Items(items: List[Expr]) extends Expr
// the terms of ACSL: \result, \old(e), \at(e, L) at the labels Pre, Here, and LoopEntry, \valid and \valid_read,
// which are true, since memory safety is not checked, and the quantifiers \forall and \exists over typed variables
case object Result extends Expr
case class Old(expr: Expr) extends Expr
case class At(expr: Expr, label: String) extends Expr
case object Valid extends Expr
case class Quant(quant: String, bound: List[(Type, String)], body: Expr) extends Expr

object IntType:
  val int = IntType(true, "int")

  // the ranks in increasing order, which decide the usual arithmetic conversions (see Parser.common)
  val ranks = List("char", "short", "int", "long", "longlong")

  // the integer type of the words of a declaration, e.g. unsigned long int
  def apply(words: List[String]): IntType =
    val longs = words.count(_ == "long")
    val rank =
      if words.contains("char") then "char"
      else if words.contains("short") then "short"
      else if longs == 1 then "long"
      else if longs > 1 then "longlong"
      else "int"
    IntType(!words.contains("unsigned"), rank)

object Num extends (String => Expr)
object FloatNum extends (String => Expr)
object Id extends (String => Expr)
object Call extends ((String, List[Expr]) => Expr)
object App extends ((String, List[Expr]) => Expr)
object Cond extends ((Expr, Option[(Expr, Expr)]) => Expr)
object Cast extends ((Type, Expr) => Expr)
object SizeofType extends (List[String] => Expr)
object SizeofExpr extends (Expr => Expr)
object Items extends (List[Expr] => Expr)
object Old extends (Expr => Expr)
object At extends ((Expr, String) => Expr)
object Quant extends ((String, List[(Type, String)], Expr) => Expr)

// the clauses of ACSL annotations by their keywords, e.g. requires, loop invariant, assert, whose argument is a term,
// except for those of assigns and loop assigns, which are not checked (see Parser.clauses)
case class Clause(kind: String, arg: Option[Expr])

// pointers, and the sizes of arrays, one per dimension, which are optional, e.g. int a[] = { 1, 2 }
case class Declarator(pointer: Boolean, name: String, sizes: List[Option[Expr]], init: Option[Expr])
object Declarator extends ((Boolean, String, List[Option[Expr]], Option[Expr]) => Declarator)

sealed trait Stmt
// the words of the integer type of a declaration, e.g. unsigned char, for sizeof of its variables (see Parser.bytes)
case class Decl(typ: Type, words: List[String], decls: List[Declarator]) extends Stmt
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
// labels are dropped, a goto resolves the statement of its label in its place (see Parser.goto)
case class Labeled(label: String, stmt: Stmt) extends Stmt
case class Goto(label: String) extends Stmt
// a switch, whose cases are labels of the statements of its body, case c: or default: (None)
case class Switch(test: Expr, body: List[Stmt]) extends Stmt
case class Case(value: Option[Expr], stmt: Stmt) extends Stmt
// the annotations of ACSL in statements, a loop with its clauses, and an assertion
case class Annotated(clauses: List[Clause], loop: Stmt) extends Stmt
case class Assertion(phi: Expr) extends Stmt

object Decl extends ((Type, List[String], List[Declarator]) => Decl)
object Assign extends ((Expr, String, Expr) => Stmt)
object ExprStmt extends (Expr => Stmt)
object If extends ((Expr, Stmt, Option[Stmt]) => Stmt)
object While extends ((Expr, Stmt) => Stmt)
object DoWhile extends ((Stmt, Expr) => Stmt)
object For extends ((Option[Stmt], Option[Expr], Option[Stmt], Stmt) => Stmt)
object Return extends (Option[Expr] => Stmt)
object Block extends (List[Stmt] => Block)
object Labeled extends ((String, Stmt) => Stmt)
object Goto extends (String => Stmt)
object Switch extends ((Expr, List[Stmt]) => Stmt)
object Case extends ((Option[Expr], Stmt) => Stmt)
object Annotated extends ((List[Clause], Stmt) => Stmt)
object Assertion extends (Expr => Stmt)

sealed trait Top
case class Global(decl: Decl) extends Top
// the names of types are replaced by their definitions by the scanner (see Typedefs)
case object Typedef extends Top
case class Function(typ: Type, name: String, params: List[(Type, String)], body: Option[Block]) extends Top
// the contract of ACSL of the function that follows (see Parser.resolve)
case class Contract(clauses: List[Clause]) extends Top

object Global extends (Decl => Top)
object Function extends ((Type, String, List[(Type, String)], Option[Block]) => Top)
object Contract extends (List[Clause] => Top)

case class Loop(test: Option[Expr], body: Stmt, step: Option[Stmt]) extends Stmt
