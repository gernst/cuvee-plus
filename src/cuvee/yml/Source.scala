package cuvee.yml

import java.io.File
import java.io.FileReader
import java.io.Reader

import scala.util.control.NonFatal

import cuvee.Config
import cuvee.Error
import cuvee.Lang
import cuvee.core._

// SV-COMP task definitions defer to the frontend of their input file, by its extension, e.g. C or SV-LIB,
// which is relative to the directory of the task definition (the input of the configuration);
// the task is read on demand, such that its errors are reported by the pipeline;
// its data model is passed on to the C frontend, the properties are not used yet
object Source extends cuvee.pipe.Source:
  // the task definition in `file` with the input file that it refers to
  def load(file: String): (Task, File) =
    val reader = new FileReader(file)
    val task =
      try Task.load(reader)
      finally reader.close()
    (task, input(Some(file), task))

  def input(file: Option[String], task: Task): File =
    val dir = file.map(file => new File(file).getAbsoluteFile.getParentFile)
    if new File(task.input).isAbsolute
    then new File(task.input)
    else new File(dir.orNull, task.input)

  // the language of the input file of the task definition `file`, by its extension,
  // C if the task cannot be read, which is reported by the pipeline when it is
  def lang(file: Option[String]): Lang =
    try
      file match
        case Some(file) =>
          val (task, _) = load(file)
          lang(task)

        case None =>
          Lang.c
    catch case NonFatal(_) => Lang.c

  def lang(task: Task): Lang =
    import Config.suffix
    Config.langs.get(task.input.suffix) match
      case Some(lang) if lang != Lang.yml => lang
      case _                              => Error.raise("unsupported language of input file", task.input)

  def newScanner(reader: Reader) =
    cuvee.c.Source.newScanner(reader)

  // the parser of the language of the input file, whose state is the initial state of the pipeline
  def newParser(config: Config) =
    lang(config.file).source.newParser(config)

  override def input(config: Config, reader: Reader, parser: easyparse.Parser[List[Cmd]]): LazyList[Cmd] =
    val task = Task.load(reader)
    val input = this.input(config.file, task)

    // reported as written in the task, independent of the directory that it is in
    Error.report("input file of task not found", task.input):
      require(input.isFile)

    // the data model of the task overrides the command line
    val arch =
      task.model match
        case Some("ILP32") => 32
        case Some("LP64")  => 64
        case Some(model)   => Error.raise("unsupported data model", model)
        case None          => config.arch

    // the parser of the frontend for the data model of the task, whose state and prelude are those of `parser`
    val config_ = config.copy(arch = arch)
    val source = lang(task).source
    val (_, parser_, _) = source.newParser(config_)
    source.input(config_, new FileReader(input), parser_)

  // no further definitions
  def preludes(config: Config): List[String] =
    Nil
