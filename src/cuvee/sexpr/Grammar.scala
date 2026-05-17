package cuvee.sexpr

import cuvee.util._

object Grammar:
  val lp = Tok.Lit("(")
  val rp = Tok.Lit(")")
  val eof = Tok.Lit("<eof>")

  def id(name: String) = Tok.Val("id", Id(name))
  def kw(name: String) = Tok.Val("kw", Kw(name))

  def str(text: String): Tok = ???
  def num(text: String): Tok = ???
  def dec(text: String): Tok = ???
  def hex(text: String): Tok = ???
  def bin(text: String): Tok = ???

  val sexprs: Pat = ???

  val sexpr = a(
    v("id"),
    $("(", sexprs, ")"),

    v("kw")
  )
