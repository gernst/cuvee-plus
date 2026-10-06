package cuvee.yml

import java.io.File
import java.io.FileReader
import java.io.Reader

import cuvee.Error
import cuvee.core._

// SV-COMP task definitions defer to the C frontend for their input file,
// which is relative to the directory of the task definition (the input of the configuration);
// the task is read on demand, such that its errors are reported by the pipeline;
// the properties are not used yet
object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    cuvee.c.Source.newScanner(reader)

  def newParser() =
    cuvee.c.Source.newParser()

  override def preludes(config: cuvee.Config) =
    cuvee.c.Source.preludes(config)

  override def input(config: cuvee.Config, reader: Reader, parser: easyparse.Parser[List[Cmd]]): LazyList[Cmd] =
    val task = Task.load(reader)
    val dir = config.input.map(file => new File(file).getAbsoluteFile.getParentFile)
    val input =
      if new File(task.input).isAbsolute
      then new File(task.input)
      else new File(dir.orNull, task.input)

    Error.report("input file of task not found", input):
      require(input.isFile)

    cuvee.c.Source.input(config, new FileReader(input), parser)
