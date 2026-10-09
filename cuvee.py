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
    (examples/sv-comp) by trace equation systems, whose goals the simplifier closes with a database of lemmas
    (cuvee.xml passes -teq -simplify).
    The output is in the language of the input, SMT-LIB for C and Dafny for Dafny: no goal left means that the
    property holds, goals that remain are not refuted, hence the result is unknown, since the tool does not produce
    witnesses of violations.
    """

    REQUIRED_PATHS = ["Cuvee.sh", "cuvee.jar"]

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

    def determine_result(self, run):
        lines = list(run.output)
        for i, line in enumerate(lines):
            # errors, e.g. constructs of C that are not supported, or rewriting that does not terminate,
            # whose message is the first string at the error or on the lines after it, e.g. (error "parse error" ...)
            if line.startswith("(error") or line.startswith("error") or line.startswith("Exception in thread"):
                message = re.search(r'"([^"]*)"', " ".join(lines[i:i + 3]))
                return result.RESULT_ERROR + (" (" + message.group(1) + ")" if message else "")

        if run.exit_code.value not in (0, None):
            return result.RESULT_ERROR

        for line in run.output:
            if line.startswith("(goal") or line.startswith("goal"):
                return result.RESULT_UNKNOWN

        return result.RESULT_TRUE_PROP
