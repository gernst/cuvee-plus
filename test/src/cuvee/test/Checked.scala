package cuvee.test

import utest._

// the examples of each language, below examples/<language>/<module>/, each a test of the command line
// in its first line (see Examples.checked and cuvee.test.Expected)
object Dafny extends TestSuite:
  val tests =
    Examples.checked(os.sub / "dafny", "dfy")

object Boogie extends TestSuite:
  val tests =
    Examples.checked(os.sub / "boogie", "bpl")

object C extends TestSuite:
  val tests =
    Examples.checked(os.sub / "c", "c")

object SmtLib extends TestSuite:
  val tests =
    Examples.checked(os.sub / "smtlib", "smt2")

object Yml extends TestSuite:
  val tests =
    Examples.checked(os.sub / "yml", "yml")

// the translations of SV-COMP tasks (examples/sv-comp), checked against the database of their expected results
// (see cuvee.test.Database), only if the environment variable CUVEE_SVCOMP is set, since they take minutes;
// otherwise only the database is read, if it exists (the translations are not part of the repository)
object SVComp extends TestSuite:
  val database = Examples.root / "sv-comp" / "expected.csv"

  val rows =
    if os.exists(database)
    then cuvee.test.Database.read(database.toNIO)
    else Nil

  val tests =
    if sys.env.contains("CUVEE_SVCOMP")
    then
      Examples.tests(rows.map(row => Examples.workspace / os.RelPath(row.file))): file =>
        val row = rows.find(row => Examples.workspace / os.RelPath(row.file) == file).get
        println("./Cuvee.sh -test " + row.file)
        cuvee.test.Database.check(Examples.workspace.toNIO, List(row)).mkString("\n") ==> ""
    else
      Tests:
        test("database"):
          for row <- rows
          do assert(Set("safe", "unsafe").contains(row.verdict), row.goals == "error" || row.goals.toIntOption.isDefined)
