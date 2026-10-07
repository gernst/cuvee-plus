package cuvee.c

import java.io.Reader

import cuvee.Config

// C starts from the state and the declarations of the SMT-LIB prelude, the parser builds expressions on Int and Bool directly,
// hence no overloaded operators remain to be resolved;
// the whole translation unit is parsed at once, such that the modified global variables can be inferred
object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    new Typedefs(new Scanner(reader))

  // the translation unit is resolved for the data model of the configuration,
  // in the state of the prelude of SMT-LIB extended by the background theory of C, which is written in Boogie
  def newParser(config: Config) =
    val (init, _, prelude) = cuvee.smtlib.Source.newParser(config)

    val boogie = new cuvee.boogie.Parser(init)
    val lifted =
      for
        cmd <- cuvee.boogie.Grammar.cmd
        cmd_ <- boogie.resolve(cmd)
      yield cmd_
    val background = cuvee.boogie.Source.parse("/cuvee/c/prelude.bpl", lifted)

    val parser = new Parser(boogie.state, config.arch)
    (boogie.state, Grammar.unit.map(parser.resolve), prelude ++ background)
