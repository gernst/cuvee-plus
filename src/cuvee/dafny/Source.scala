package cuvee.dafny

import java.io.Reader
import java.nio.file.Files
import java.nio.file.Path

import cuvee.Config
import cuvee.Error
import cuvee.core.Cmd
import cuvee.core.State

object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    new Scanner(reader)

  // the commands of `parser`, each resolved in its state
  def lifted(parser: Parser) =
    for
      cmd <- Grammar.cmd;
      cmd_ <- parser.resolve(cmd)
    yield cmd_

  // the includes of the input are relative to its directory, the working directory if it is not a file
  def newParser(config: Config) =
    val parser = new Parser(State.empty)
    val prelude = parse("/cuvee/dafny/prelude.dfy", lifted(parser))

    // the parser's state now contains the declarations of the prelude
    val init = parser.state
    val dir = config.file.map(Path.of(_).toAbsolutePath.getParent).getOrElse(Path.of(""))
    parser.include = included(init, dir, _)
    (init, lifted(parser), prelude)

  // the commands of the file `path` of an include in the directory `dir`, parsed by a fresh parser that starts from
  // `init`, the state after the prelude, which is immutable, hence shared by all includes; the includes of the file
  // are relative to its own directory
  def included(init: State, dir: Path, path: String): List[Cmd] =
    val file = dir.resolve(path)

    // reported as written, independent of the directory
    Error.report("included file not found", path):
      require(Files.isRegularFile(file))

    val parser = new Parser(init)
    parser.include = included(init, file.toAbsolutePath.getParent, _)
    include(file.toString, lifted(parser))

  // with -hybrid, the definitions of parallel composition
  override def preludes(config: Config) =
    if config.input.features.contains("hybrid")
    then List("/cuvee/dafny/hybrid.dfy")
    else Nil
