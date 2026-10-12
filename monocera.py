# MonoCera of the CAV 2023 artifact (TriCera with instrumentation for aggregates, tools/monocera/tricera):
# tri with the options of the artifact's run-list-monocera-cav23, -heaparrays -abstractPO -onlyexq, and -t:<s>
# from the CPU time limit; it answers SAFE, UNSAFE, or UNKNOWN on its own line
import benchexec.result as result
import benchexec.tools.template


class Tool(benchexec.tools.template.BaseTool2):
    REQUIRED_PATHS = ["tri", "triEnv", "tri-pp", "target"]

    def executable(self, tool_locator):
        return tool_locator.find_executable("tri")

    def program_files(self, executable):
        return self._program_files_from_executable(executable, self.REQUIRED_PATHS)

    def name(self):
        return "MonoCera"

    def version(self, executable):
        return "cav23"

    def cmdline(self, executable, options, task, rlimits):
        timeout = [] if any(o.startswith("-t:") for o in options) or not rlimits.cputime else ["-t:" + str(rlimits.cputime)]
        return [executable, *options, *timeout, task.single_input_file]

    def determine_result(self, run):
        for line in run.output:
            answer = line.strip()
            if answer == "SAFE":
                return result.RESULT_TRUE_PROP
            if answer == "UNSAFE":
                return result.RESULT_FALSE_REACH
            if answer in ("UNKNOWN", "TIMEOUT", "timeout"):
                return result.RESULT_UNKNOWN
        if run.exit_code.value not in (0, None):
            return result.RESULT_ERROR
        return result.RESULT_UNKNOWN
