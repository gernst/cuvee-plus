package cuvee.test

import utest._

// the statements of the lemmas of the stable modules of the database in Lean (lean/TEQ/Database.lean, Check.lean) are
// those that the current modules print: scripts/lean/generate.py --check prints them with the classpath of this JVM
// and compares, without writing, so a changed module whose statements were not regenerated fails here, without Lean;
// the proofs themselves are checked by scripts/lean/check.sh
object Lean extends TestSuite:
  val tests = Tests:
    test("statements"):
      val root = Examples.root / os.up
      val classpath = System.getProperty("java.class.path")
      val result = os.proc("python3", root / "scripts" / "lean" / "generate.py", "--check", "--classpath", classpath)
        .call(cwd = root, check = false, mergeErrIntoOut = true, timeout = 300000)
      if result.exitCode != 0 then throw java.lang.AssertionError(result.out.text())
