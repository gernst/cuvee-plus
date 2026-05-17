package cuvee.boogie

import cuvee.util._

object Grammar:
  val name = v("name")

  val typ = a(
    "bool",
    "int",
    "real"
  )

  val formal = $(name, ":", typ)
  val params = ???
  val formals = ???

  val cmd = a(
    $("const", name, ":", typ) ~>
      $("declare-const", 1, 2),

    $("function", name, "(", formals, ")", ":", typ) ~>
      $("declare-fun", 1, 2, 3),

    $("function", name, "<", params, ">", "(", formals, ")", ":", typ) ~>
      $("declare-fun", 1, $("par", 2, 3, 4))
  )

@main
def test() =
  ???
