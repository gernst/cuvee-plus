#!/usr/bin/env python3
"""portfolio.py [options] <file>: Cuvée's methods in parallel on a task, the answer of the first that is definite,
after which the others are stopped (ideas/portfolio.md); a method may have a timeout of CPU time (the fuzzer), the
others run until they answer or the limit of the run ends them. The options are passed to
every method of Cuvée (e.g. -arch 32, -unbounded, -witness witness.yml).

The output is that of the method that answers, so the tool-info module reads it as Cuvée's (benchexec cuvee.py): a line
"incorrect" is false, only "correct" lines are true. Each method of Cuvée writes its witness to a file of its own,
the one of the method that answers is copied to the file of -witness. portfolio.py -version is Cuvée's version. Open
are the replay of a trace of fuzzing and its witness."""

import os
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed

HERE = os.path.dirname(os.path.abspath(__file__))

# the process groups that are running, stopped once a method has answered
RUNNING = set()
STOPPED = threading.Event()
LOCK = threading.Lock()


def language(file):
    if file.endswith((".c", ".i")):
        return "c"
    if file.endswith(".svlib"):
        return "svlib"
    return "other"


def limited(seconds):
    # in the child: its own process group, such that z3 and the compiled task end with it, and a hard limit of CPU
    # time, which is what SV-COMP measures, if any
    def preexec():
        os.setsid()
        if seconds is not None:
            limit = max(1, int(seconds))
            resource.setrlimit(resource.RLIMIT_CPU, (limit, limit + 1))
    return preexec


def run(command, seconds=None):
    # the output of a command, within `seconds` of CPU time (and a wall-clock guard of twice that) if given, "" if it
    # is killed or if the portfolio has stopped
    with LOCK:
        if STOPPED.is_set():
            return ""
        proc = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                text=True, preexec_fn=limited(seconds))
        RUNNING.add(proc.pid)
    try:
        out, _ = proc.communicate(timeout=None if seconds is None else 2 * seconds + 5)
        return out
    except subprocess.TimeoutExpired:
        kill(proc.pid)
        proc.communicate()
        return ""
    finally:
        with LOCK:
            RUNNING.discard(proc.pid)


def kill(pid):
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def stop():
    # no new processes, and the running ones killed
    with LOCK:
        STOPPED.set()
        for pid in RUNNING:
            kill(pid)


def answer(output):
    # as the tool-info module: false if a goal is incorrect, true if all are correct, otherwise none
    answers = {line.strip() for line in output.splitlines() if line.strip() in ("correct", "incorrect", "unknown")}
    if "incorrect" in answers:
        return "false"
    if answers == {"correct"}:
        return "true"
    return None


class Method:
    """A method of the portfolio: its name and the languages of the tasks it applies to; `run` gives its answer
    ("true", "false", or None) and the output to print with it."""

    def __init__(self, name, languages):
        self.name = name
        self.languages = languages

    def applies(self, file):
        return language(file) in self.languages

    def run(self, options, file):
        raise NotImplementedError


class Cuvee(Method):
    """Cuvée with the options of the method and those of the portfolio, by the native binary if there is one (make
    native), which needs no JVM, otherwise by the jar."""

    def __init__(self, name, languages, options):
        super().__init__(name, languages)
        self.options = options

    def command(self):
        if os.path.exists(os.path.join(HERE, "cuvee.native")):
            return [os.path.join(HERE, "Cuvee-native.sh")]
        return [os.path.join(HERE, "Cuvee.sh")]

    def run(self, options, file):
        output = run(self.command() + self.options + self.witnessed(options) + [file])
        return answer(output), output

    def witnessed(self, options):
        # the witness to a file of this method, e.g. witness.fallback.yml for witness.yml
        if "-witness" not in options:
            return options
        i = options.index("-witness")
        return options[:i + 1] + [witness(options[i + 1], self.name)] + options[i + 2:]


class Fuzz(Method):
    """Korn's fuzzer (../korn, korn.tool.Fuzz): the task compiled with its harness in fuzz/ (fuzz/README.md),
    __VERIFIER.c, which maps the nondet functions to __VERIFIER_next_nondet, and __VERIFIER_random.c, which draws small
    values, records them, and prints "unsat" and the trace when reach_error is reached; each run ends after one second,
    runs repeat until the timeout in seconds of CPU time."""

    harness = ["fuzz/__VERIFIER.c", "fuzz/__VERIFIER_random.c"]

    def __init__(self, name, languages, timeout):
        super().__init__(name, languages)
        self.timeout = timeout

    def run(self, options, file):
        harness = [os.path.join(HERE, f) for f in self.harness]
        if not all(os.path.exists(f) for f in harness):
            return None, ""
        arch = ["-m32"] if "-arch" in options and options[options.index("-arch") + 1] == "32" else []
        with tempfile.TemporaryDirectory() as tmp:
            binary = os.path.join(tmp, "fuzz")
            compiled = subprocess.run(["gcc", "-w", "-O1", *arch, "-o", binary, file, *harness],
                                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if compiled.returncode != 0:
                return None, ""
            # the CPU time of the runs, each limited to 2 s, counted by their number, since getrusage of the children
            # mixes all methods
            runs = 0
            while runs * 2 < self.timeout and not STOPPED.is_set():
                runs += 1
                lines = run([binary], 2).splitlines()
                if lines and lines[0] == "unsat":
                    # TODO: replay the trace (Korn's Confirm, __VERIFIER_counterexample.c), write the violation witness
                    return "false", "incorrect\n"
        return None, ""


# the methods, in parallel, sharing the CPU time that SV-COMP gives the run (900 s for all processes together); z3 is
# limited by that time only, since -timeout defaults to 1 s per query
METHODS = [
    Fuzz("fuzz", ["c"], timeout=30),
    Cuvee("fallback", ["c", "svlib"], ["-svcomp", "-rules", "-fallback", "-z3", "-timeout", "900000"]),
    Cuvee("chc", ["c", "svlib"], ["-chc", "-prove", "-z3", "-timeout", "900000"]),
    # bounded unrolling (ideas/prove-next.md, plan B), once -unroll exists
]


def witness(file, name):
    base, ext = os.path.splitext(file)
    return f"{base}.{name}{ext}"


def main(args):
    if args == ["-version"]:
        return subprocess.run(Cuvee("version", [], []).command() + args).returncode

    *options, file = args
    methods = [m for m in METHODS if m.applies(file)]

    with ThreadPoolExecutor(max_workers=len(methods) or 1) as pool:
        futures = {pool.submit(m.run, options, file): m for m in methods}
        for future in as_completed(futures):
            result, output = future.result()
            print(f"; portfolio: {futures[future].name}: {result or 'unknown'}", file=sys.stderr)
            if result:
                stop()
                method = futures[future]
                if "-witness" in options:
                    requested = options[options.index("-witness") + 1]
                    if os.path.exists(witness(requested, method.name)):
                        shutil.copy(witness(requested, method.name), requested)
                sys.stdout.write(output)
                return 0
    print("unknown")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
