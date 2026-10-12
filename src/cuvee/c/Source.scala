package cuvee.c

import java.io.Reader

import cuvee.Config
import cuvee.core.State

// C starts from its prelude, which includes the core theory, whose arithmetic is on Int only,
// hence the parser builds expressions on Int and Bool directly, without overloaded operators;
// the whole translation unit is parsed at once, such that the modified global variables can be inferred
object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    new Typedefs(new Scanner(reader))

  // the translation unit is resolved for the data model of the configuration,
  // in the state of the prelude, which is written in Boogie
  def newParser(config: Config) =
    val boogie = new cuvee.boogie.Parser(State.empty)
    val lifted =
      for
        cmd <- cuvee.boogie.Grammar.cmd
        cmd_ <- boogie.resolve(cmd)
      yield cmd_
    val prelude = cuvee.boogie.Source.parse("/cuvee/c/prelude.bpl", lifted)

    // -teq and -chc infer the modified global variables, -vcgen takes those of assigns clauses where there are some
    val infer = config.transforms.exists(t => t == cuvee.verify.TEQ || t == cuvee.verify.Horn)
    val parser = new Parser(boogie.state, config.arch, config.unbounded, infer)
    (boogie.state, Grammar.unit.map(parser.resolve), prelude)

  // no further definitions
  def preludes(config: Config): List[String] =
    Nil
