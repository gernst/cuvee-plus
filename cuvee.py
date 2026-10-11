# This file is part of BenchExec, a framework for reliable benchmarking:
# https://github.com/sosy-lab/benchexec
#
# SPDX-License-Identifier: Apache-2.0

import re

import benchexec.result as result
import benchexec.tools.template


class Tool(benchexec.tools.template.BaseTool2):
    """
    Tool info for Cuvée, which proves the property unreach-call of C programs and of their Dafny translations
    (benchmarks/sv-comp/dafny) by trace equation systems, whose goals the simplifier closes with a database of lemmas,
    optionally followed by an SMT solver on the remaining goals.
    The output is in the language of the input, SMT-LIB for C and Dafny for Dafny: no goal left means that the
    property holds, a goal that simplifies to false that it is violated (except with -unbounded), other goals that
    remain are not refuted, hence the result is unknown; the tool does not produce witnesses of violations.
    """

    # z3 for -fallback -z3, a copy of the local one (not in git), since the machines of the cluster have none
    REQUIRED_PATHS = ["Cuvee.sh", "cuvee.jar", "z3"]

    def executable(self, tool_locator):
        return tool_locator.find_executable("Cuvee.sh")

    def program_files(self, executable):
        return self._program_files_from_executable(executable, self.REQUIRED_PATHS)

    def name(self):
        return "Cuvée"

    def version(self, executable):
        return self._version_from_tool(executable, arg="-version").replace("Cuvée", "").strip()

    def cmdline(self, executable, options, task, rlimits):
        if task.property_file and not task.property_file.endswith("unreach-call.prp"):
            raise benchexec.tools.template.UnsupportedFeatureException(
                "property not supported: " + task.property_file
            )

        data_model = task.options.get("data_model") if task.options else None
        archs = {"ILP32": ["-arch", "32"], "LP64": ["-arch", "64"]}
        arch = archs.get(data_model, [])

        return [executable] + options + arch + [task.single_input_file]

    # a goal that the simplifier refutes, printed as (goal false) or goal false, or passed on to the solver of -fallback,
    # which reports it as (error "goal does not hold" "Sat" "false")
    GOAL_FALSE = re.compile(r'^\(?goal false\)?$')
    SAT_FALSE = re.compile(r'"goal does not hold"\s+"Sat"\s+"false"')

    def determine_result(self, run):
        lines = list(run.output)

        # a refuted goal means that the property is violated, since the steps before are equivalences, except with
        # -unbounded, whose nondeterministic values range over more than their types; the other goals that remain
        # are not refuted, nor are those that the solver of -fallback does not prove, as its encoding generalizes
        if "-unbounded" not in run.cmdline:
            for i, line in enumerate(lines):
                if self.GOAL_FALSE.match(line.strip()) or self.SAT_FALSE.search(" ".join(lines[i:i + 3])):
                    return result.RESULT_FALSE_REACH

        for i, line in enumerate(lines):
            # errors, e.g. constructs of C that are not supported, or rewriting that does not terminate,
            # whose message is the first string at the error or on the lines after it, e.g. (error "parse error" ...);
            # goals that the solver of -fallback does not prove are not refuted, since the encoding generalizes
            if line.startswith("(error") or line.startswith("error") or line.startswith("Exception in thread"):
                message = re.search(r'"([^"]*)"', " ".join(lines[i:i + 3]))
                if message and message.group(1) == "goal does not hold":
                    return result.RESULT_UNKNOWN
                return result.RESULT_ERROR + (" (" + message.group(1) + ")" if message else "")

        if run.exit_code.value not in (0, None):
            return result.RESULT_ERROR

        for line in run.output:
            if line.startswith("(goal") or line.startswith("goal"):
                return result.RESULT_UNKNOWN

        return result.RESULT_TRUE_PROP
