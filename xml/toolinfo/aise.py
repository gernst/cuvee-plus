# AISE as in benchexec.tools.aise, but uploads the whole tool to the cluster:
# that module declares no REQUIRED_PATHS, so --tool-directory transfers only bin/aise
import benchexec.tools.aise


class Tool(benchexec.tools.aise.Tool):
    REQUIRED_PATHS = ["bin", "aise_build", "lib", "llvm12", "property"]

    def program_files(self, executable):
        return self._program_files_from_executable(
            executable, self.REQUIRED_PATHS, parent_dir=True
        )
