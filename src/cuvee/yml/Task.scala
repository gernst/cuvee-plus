package cuvee.yml

import java.io.Reader

import scala.jdk.CollectionConverters._

import org.snakeyaml.engine.v2.api.Load
import org.snakeyaml.engine.v2.api.LoadSettings
import org.snakeyaml.engine.v2.exceptions.YamlEngineException

import cuvee.Error

// a property of a task: the file that specifies it, e.g. unreach-call.prp,
// whether it holds, and for memory safety the part that fails
case class Property(file: String, expected: Option[Boolean], subproperty: Option[String])

// an SV-COMP task definition (format version 2.0), of which only a single C input file is supported:
//
//   format_version: '2.0'
//   input_files: 'count.c'
//   properties:
//     - property_file: ../properties/unreach-call.prp
//       expected_verdict: true
//   options:
//     language: C
//     data_model: ILP32
case class Task(input: String, properties: List[Property], language: String, model: Option[String])

object Task:
  // the document is loaded into Java maps, lists, and scalars, which are converted by pattern matching
  def load(reader: Reader): Task =
    val doc =
      try Load(LoadSettings.builder().build()).loadFromReader(reader)
      catch case e: YamlEngineException => Error.raise("malformed task definition", e.getMessage)

    val task = map(doc, "task definition")

    val input =
      task.get("input_files") match
        case Some(file: String) => file
        case Some(files: java.util.List[?]) =>
          files.asScala.toList match
            case List(file: String) => file
            case _                  => Error.raise("only a single input file is supported", files)
        case Some(other) => Error.raise("malformed input files", other)
        case None        => Error.raise("task definition without input files")

    val properties =
      task.get("properties") match
        case Some(props: java.util.List[?]) => props.asScala.toList.map(property)
        case Some(other)                    => Error.raise("malformed properties", other)
        case None                           => Nil

    val options =
      task.get("options") match
        case Some(opts) => map(opts, "options")
        case None       => Map()

    val language =
      options.get("language") match
        case Some("C") | None => "C"
        case Some(other)      => Error.raise("unsupported language of task", other)

    val model =
      options.get("data_model") match
        case Some(model: String) => Some(model)
        case Some(other)         => Error.raise("malformed data model", other)
        case None                => None

    Task(input, properties, language, model)

  def property(value: Any): Property =
    val prop = map(value, "property")

    val file =
      prop.get("property_file") match
        case Some(file: String) => file
        case _                  => Error.raise("property without property file", value)

    val expected =
      prop.get("expected_verdict") match
        case Some(verdict: java.lang.Boolean) => Some(verdict.booleanValue)
        case Some(other)                      => Error.raise("malformed expected verdict", other)
        case None                             => None

    val subproperty =
      prop.get("subproperty") match
        case Some(sub: String) => Some(sub)
        case Some(other)       => Error.raise("malformed subproperty", other)
        case None              => None

    Property(file, expected, subproperty)

  // a mapping with string keys
  def map(value: Any, what: String): Map[String, Any] =
    value match
      case m: java.util.Map[?, ?] =>
        m.asScala.toMap.map:
          case (key: String, value) => key -> value
          case (key, _)             => Error.raise("malformed key in " + what, key)

      case _ =>
        Error.raise("malformed " + what, value)
