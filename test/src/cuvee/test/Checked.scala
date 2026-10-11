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

object SvLib extends TestSuite:
  val tests =
    Examples.checked(os.sub / "svlib", "svlib")

// the translations of SV-COMP tasks (benchmarks/sv-comp/dafny), checked against the database of their expected results
// (see cuvee.test.Database), only if the environment variable CUVEE_SVCOMP is set, since they take minutes;
// otherwise only the database is read, if it exists;
// a run that is much slower or much faster than recorded fails: then the expected results must NOT be regenerated
// before the change of performance is understood, a slower run may be a performance degradation of the simplifier or
// the lemmas, and a run that ends much faster is likely a soundness bug, e.g. goals closed by mistake
object SVComp extends TestSuite:
  val tests =
    Databases.checked(Examples.workspace / "benchmarks" / "sv-comp" / "dafny" / "expected.csv", timed = true)

// the C programs printed from these translations (benchmarks/sv-comp/c), with the expected results of the Dafny ones,
// without times
object SVCompC extends TestSuite:
  val tests =
    Databases.checked(Examples.workspace / "benchmarks" / "sv-comp" / "c" / "expected.csv", timed = false)

// the rows of a database, whose times are required if `timed`
object Databases:
  def checked(database: os.Path, timed: Boolean): Tests =
    val rows =
      if os.exists(database)
      then cuvee.test.Database.read(database.toNIO)
      else Nil

    if sys.env.contains("CUVEE_SVCOMP")
    then
      Examples.tests(rows.map(row => Examples.workspace / os.RelPath(row.file))): file =>
        val row = rows.find(row => Examples.workspace / os.RelPath(row.file) == file).get
        println("./Cuvee.sh -test " + row.file)
        cuvee.test.Database.check(Examples.workspace.toNIO, List(row)).mkString("\n") ==> ""
    else
      Tests:
        // rows whose goals are timeout record runs that did not end, without a time (see cuvee.test.Database)
        test("database"):
          for row <- rows
          do
            val timeout = row.goals == "timeout"
            assert(Set("safe", "unsafe").contains(row.verdict), timeout || row.goals == "error" || row.goals.toIntOption.isDefined, !timed || timeout || row.time.isDefined)
