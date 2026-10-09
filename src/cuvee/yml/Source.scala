package cuvee.yml

import java.io.File
import java.io.FileReader
import java.io.Reader

import cuvee.Config
import cuvee.Error
import cuvee.core._

// SV-COMP task definitions defer to the C frontend for their input file,
// which is relative to the directory of the task definition (the input of the configuration);
// the task is read on demand, such that its errors are reported by the pipeline;
// its data model is passed on to the C frontend, the properties are not used yet
object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    cuvee.c.Source.newScanner(reader)

  def newParser(config: Config) =
    cuvee.c.Source.newParser(config)

  override def input(config: Config, reader: Reader, parser: easyparse.Parser[List[Cmd]]): LazyList[Cmd] =
    val task = Task.load(reader)
    val dir = config.file.map(file => new File(file).getAbsoluteFile.getParentFile)
    val input =
      if new File(task.input).isAbsolute
      then new File(task.input)
      else new File(dir.orNull, task.input)

    Error.report("input file of task not found", input):
      require(input.isFile)

    // the data model of the task overrides the command line
    val arch =
      task.model match
        case Some("ILP32") => 32
        case Some("LP64")  => 64
        case Some(model)   => Error.raise("unsupported data model", model)
        case None          => config.arch

    // the parser of the C frontend for the data model of the task, whose state and prelude are those of `parser`
    val config_ = config.copy(arch = arch)
    val (_, parser_, _) = cuvee.c.Source.newParser(config_)
    cuvee.c.Source.input(config_, new FileReader(input), parser_)

  // no further definitions
  def preludes(config: Config): List[String] =
    Nil
