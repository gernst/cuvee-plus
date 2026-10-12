# This file is part of BenchExec, a framework for reliable benchmarking:
# https://github.com/sosy-lab/benchexec
#
# SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

import re

import benchexec.tools.template
from benchexec import result
from benchexec.tools.sv_benchmarks_util import ILP32, LP64, get_data_model_from_task


class Tool(benchexec.tools.template.BaseTool2):
    """
    Tool info for Cuvée, a deductive verifier that proves the property unreach-call
    of C programs without loop invariants: it summarizes loops by trace equation
    systems, whose goals it closes by rewriting with a database of lemmas,
    optionally followed by the SMT solver Z3 on the goals that remain (-fallback -z3).

    No goal left means that the property holds. A goal that simplifies to false
    means that it is violated, except with the option -unbounded, under which
    nondeterministic values range over all integers. Other goals that remain are
    not refuted, hence the result is unknown, also those that Z3 refutes, since
    the encoding for it abstracts the goal. With -chc -z3, Cuvée translates the
    program into constrained Horn clauses, and the answer of Z3 is the result: sat
    (the property holds), unsat (it is violated, except with -unbounded), or
    unknown. Cuvée does not produce witnesses.

    For the property correct-tags (formerly correct-annotations) of SV-LIB scripts, Cuvée checks the
    annotations by verification conditions (-vcgen -z3) or by constrained Horn
    clauses (-chc -z3). A goal that Z3 refutes, or unsatisfiable clauses, mean that
    an annotation is violated, no refuted goal or satisfiable clauses that all of
    them hold. The verification conditions need the invariants of all loops, i.e.,
    validation tasks, whereas the Horn clauses infer them.

    With -verify, Cuvée decides the result itself: it answers correct, incorrect, or
    unknown to each verify-call of SV-LIB, or once to other inputs, whether the
    program satisfies its specification, and only these answers determine the result.
    """

    # z3 next to Cuvee.sh, which puts its own directory first on the PATH
    REQUIRED_PATHS = ["Cuvee.sh", "cuvee.jar", "z3"]

    # a goal that the simplifier refutes, printed as (goal false) or goal false;
    # a model of Z3 for a goal passed on to it, (error "goal does not hold" "Sat" ...),
    # is no counterexample, since the encoding generalizes the goal (see below)
    GOAL_FALSE = re.compile(r"^\(?goal false\)?$")

    def executable(self, tool_locator):
        return tool_locator.find_executable("Cuvee.sh")

    def program_files(self, executable):
        return self._program_files_from_executable(executable, self.REQUIRED_PATHS)

    def name(self):
        return "Cuvée"

    def project_url(self):
        return "https://github.com/gernst/cuvee-plus"

    def version(self, executable):
        version = self._version_from_tool(executable, arg="-version")
        return version.replace("Cuvée", "").strip()

    def cmdline(self, executable, options, task, rlimits):
        if task.property_file and not task.property_file.endswith(
            ("unreach-call.prp", "correct-tags.prp", "correct-annotations.prp")
        ):
            raise benchexec.tools.template.UnsupportedFeatureException(
                "property not supported: " + task.property_file
            )

        arch = get_data_model_from_task(
            task, {ILP32: ["-arch", "32"], LP64: ["-arch", "64"]}
        )
        if arch is None or "-arch" in options:
            arch = []

        return [executable, *options, *arch, task.single_input_file]

    def determine_result(self, run):
        lines = list(run.output)

        if "-verify" in run.cmdline:
            return self.determine_answers(run, lines)

        if run.cmdline and run.cmdline[-1].endswith(".svlib"):
            return self.determine_svlib_result(run, lines)

        # with -chc, the answer of the solver to the Horn clauses, unless an error
        # comes first; unsat is a counterexample to the semantics of C, which
        # -unbounded does not model
        if "-chc" in run.cmdline:
            for line in lines:
                answer = line.strip()
                if answer.startswith(("(error", "error", "Exception in thread")):
                    break
                if answer == "sat":
                    return result.RESULT_TRUE_PROP
                if answer == "unsat" and "-unbounded" not in run.cmdline:
                    return result.RESULT_FALSE_REACH
                if answer in ("unsat", "unknown"):
                    return result.RESULT_UNKNOWN

        # a refuted goal, since the steps before are equivalences,
        # except with -unbounded
        if "-unbounded" not in run.cmdline:
            for line in lines:
                if self.GOAL_FALSE.match(line.strip()):
                    return result.RESULT_FALSE_REACH

        # errors, e.g. constructs of C that are not supported, or rewriting that
        # does not terminate, whose message is the first string at the error or on
        # the lines after it, e.g. (error "parse error" ...); goals that the solver
        # does not prove are not refuted, since the encoding for it generalizes
        for i, line in enumerate(lines):
            if line.startswith(("(error", "error", "Exception in thread")):
                message = re.search(r'"([^"]*)"', " ".join(lines[i : i + 3]))
                if message and message.group(1) == "goal does not hold":
                    return result.RESULT_UNKNOWN
                return result.RESULT_ERROR + (
                    " (" + message.group(1) + ")" if message else ""
                )

        if run.exit_code.value not in (0, None):
            return result.RESULT_ERROR

        for line in lines:
            if line.startswith(("(goal", "goal")):
                return result.RESULT_UNKNOWN

        # with -chc, no answer of the solver, e.g. when it was stopped
        if "-chc" in run.cmdline:
            return result.RESULT_UNKNOWN

        return result.RESULT_TRUE_PROP

    ANSWERS = ("correct", "incorrect", "unknown")

    # the answers of -verify: an incorrect one is a violation, also before an error, all of them correct means that
    # the property holds; otherwise the errors, e.g. constructs that are not supported, as above
    def determine_answers(self, run, lines):
        answers = [line.strip() for line in lines if line.strip() in self.ANSWERS]

        if "incorrect" in answers:
            if run.cmdline[-1].endswith(".svlib"):
                return result.RESULT_FALSE_PROP
            return result.RESULT_FALSE_REACH

        for i, line in enumerate(lines):
            if line.startswith(("(error", "error", "Exception in thread")):
                message = re.search(r'"([^"]*)"', " ".join(lines[i : i + 3]))
                return result.RESULT_ERROR + (
                    " (" + message.group(1) + ")" if message else ""
                )

        if run.exit_code.value not in (0, None) or not answers:
            return result.RESULT_ERROR

        if all(answer == "correct" for answer in answers):
            return result.RESULT_TRUE_PROP

        return result.RESULT_UNKNOWN

    # the answer of Z3 to a refuted goal of -vcgen, (error "goal does not hold"
    # "Sat" ...), or to one that it cannot decide
    GOAL_SAT = re.compile(r'"goal does not hold"\s+"Sat"')
    GOAL_UNKNOWN = re.compile(r'"goal does not hold"\s+"Unknown"')

    def determine_svlib_result(self, run, lines):
        text = " ".join(lines)

        # a violated annotation: the precondition of the verify-call or the goal
        # of a procedure
        if self.GOAL_SAT.search(text):
            return result.RESULT_FALSE_PROP

        if self.GOAL_UNKNOWN.search(text):
            return result.RESULT_UNKNOWN

        # get-witness, which usually ends a script, is not supported and reported
        # as an error after the verdict, which stops the run with exit code 1 but
        # does not affect the verdict
        witness = False

        for i, line in enumerate(lines):
            if line.startswith(("(error", "error", "Exception in thread")):
                context = " ".join(lines[i : i + 3])
                message = re.search(r'"([^"]*)"', context)
                if (
                    message
                    and message.group(1) == "not supported"
                    and "get-witness" in context
                ):
                    witness = True
                    continue
                return result.RESULT_ERROR + (
                    " (" + message.group(1) + ")" if message else ""
                )

        if run.exit_code.value not in (0, None) and not witness:
            return result.RESULT_ERROR

        # the clauses of -chc are checked at each verify-call and at the end:
        # unsatisfiable clauses refute an annotation, satisfiable ones at every
        # check mean that all annotations hold
        if "-chc" in run.cmdline:
            statuses = [
                line.strip()
                for line in lines
                if line.strip() in ("sat", "unsat", "unknown")
            ]
            if "unsat" in statuses:
                return result.RESULT_FALSE_PROP
            if statuses and all(status == "sat" for status in statuses):
                return result.RESULT_TRUE_PROP
            return result.RESULT_UNKNOWN

        # the goals of -teq and -vcgen that remain: a refuted one violates an
        # annotation, the others are not refuted
        goals = [line.strip() for line in lines if line.startswith(("(goal", "goal"))]
        if any(self.GOAL_FALSE.match(goal) for goal in goals):
            return result.RESULT_FALSE_PROP
        if goals:
            return result.RESULT_UNKNOWN

        return result.RESULT_TRUE_PROP
