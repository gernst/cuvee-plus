# Cuvée as in benchexec.tools.cuvee (cuvee.py), but the native executable of make native, which starts without a JVM:
# Cuvee-native.sh runs cuvee.native, both uploaded with z3 instead of Cuvee.sh and cuvee.jar
import benchexec.tools.cuvee


class Tool(benchexec.tools.cuvee.Tool):
    REQUIRED_PATHS = ["Cuvee-native.sh", "cuvee.native", "z3"]

    def executable(self, tool_locator):
        return tool_locator.find_executable("Cuvee-native.sh")

    def name(self):
        return "Cuvée (native)"
