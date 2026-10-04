package easyprint

import utest._

import Doc._

object DocTests extends TestSuite:
  // a call f(a, b, ...) whose arguments go on separate lines if it does not fit
  def call(fun: String, args: Doc*): Doc =
    Group(text(fun + "(") ++ Nest(2, linebreak ++ join(args, text(",") ++ line)) ++ text(")"))

  val tests = Tests:
    test("text"):
      render(text("a") ++ text("b") +:+ text("c"), 80) ==> List("ab c")

    test("empty"):
      render(empty, 80) ==> List("")
      render(empty ++ text("a") ++ empty, 80) ==> List("a")

    test("group fits"):
      render(call("f", "x", "y"), 80) ==> List("f(x, y)")

    test("group breaks"):
      render(call("f", "xxx", "yyy"), 6) ==> List("f(", "  xxx,", "  yyy)")

    test("exact width"):
      render(call("f", "x", "y"), 7) ==> List("f(x, y)")
      render(call("f", "x", "y"), 6) ==> List("f(", "  x,", "  y)")

    // the outer group breaks first, inner groups stay flat if they fit
    test("nested groups"):
      render(call("f", call("g", "a", "b"), call("h", "c", "d")), 12) ==>
        List("f(", "  g(a, b),", "  h(c, d))")

    test("nesting accumulates"):
      render(call("f", call("g", "aaaa", "bbbb")), 8) ==>
        List("f(", "  g(", "    aaaa,", "    bbbb))")

    // the rest of the line after a group counts for whether it fits
    test("text after group"):
      render(call("f", "x") ++ text(" + something"), 10) ==> List("f(", "  x) + something")

    test("hard line"):
      render(text("a") ++ hardline ++ text("b"), 80) ==> List("a", "b")
      render(text("a") ++ Nest(2, hardline ++ text("b")), 80) ==> List("a", "  b")

    test("hard line breaks enclosing group"):
      render(Group(text("a") ++ line ++ text("b") ++ hardline ++ text("c")), 80) ==>
        List("a", "b", "c")

    test("linebreak is empty when flat"):
      render(Group(text("a") ++ linebreak ++ text("b")), 80) ==> List("ab")

    test("trailing spaces are dropped"):
      render(text("a ") ++ hardline ++ text("b"), 80) ==> List("a", "b")

    test("lines"):
      render(Nest(2, Doc.lines(List("x", "y"))), 80) ==> List("x", "  y")

    test("long documents"):
      val doc = join((1 to 100000).map(i => text(i.toString)), line)
      render(doc, 80).length ==> 100000
      render(Group(doc), 80).length ==> 100000

    test("fill"):
      val doc = text("f(") ++ Align(Doc.fill(List("aa", "bb", "cc", "dd").map(text), text(","))) ++ text(")")
      render(doc, 80) ==> List("f(aa, bb, cc, dd)")
      render(doc, 10) ==> List("f(aa, bb,", "  cc, dd)")
