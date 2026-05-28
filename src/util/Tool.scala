package util

import java.io.PrintStream
import java.io.BufferedReader
import java.io.InputStreamReader

object Tool:
  def run(cmd: String*) =
    val process = new ProcessBuilder(cmd*)
    val status = process.start.waitFor()
    status

  def pipe(cmd: String*) =
    val builder = new ProcessBuilder(cmd*)
    val proc = builder.start()
    val in = new PrintStream(proc.getOutputStream())
    val out = new BufferedReader(new InputStreamReader(proc.getInputStream()))
    val err = proc.getErrorStream()
    (in, out, err, proc)
