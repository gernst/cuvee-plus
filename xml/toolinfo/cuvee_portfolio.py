# Cuvée as in benchexec.tools.cuvee (cuvee.py), but the portfolio of its methods (portfolio.py, ideas/portfolio.md),
# which runs them in parallel on the native executable and prints the output of the one that answers, so that the
# answers are read as Cuvée's; portfolio.py -version is Cuvée's version
import benchexec.tools.cuvee


class Tool(benchexec.tools.cuvee.Tool):
    # the script, the native executable that it runs, z3 for both methods of Cuvée, and the harness of the fuzzer, which
    # needs gcc (with -m32) on the machine
    REQUIRED_PATHS = [
        "portfolio.py",
        "Cuvee-native.sh",
        "cuvee.native",
        "z3",
        "fuzz/__VERIFIER.c",
        "fuzz/__VERIFIER_random.c",
    ]

    def executable(self, tool_locator):
        return tool_locator.find_executable("portfolio.py")

    def name(self):
        return "Cuvée (portfolio)"
