"""The SV-COMP tests in a form for Cuvée, in polished_tests/cuvee/<operator>.

Like the variants of the other tools (convert_cav23.py, run with -nomalloc as for the paper), the
macros are substituted and the arrays allocated by malloc become arrays of their size. Unlike those,
SV-COMP's harness and __VERIFIER_assert stay, which Cuvée reads. Each test gets a task definition
with the expected verdict true, which holds for all tests of the paper.

Usage: python3 convert_cuvee.py [operator/test ...], e.g. sum/brs1; without arguments, all tests.
"""

import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SVCOMP = HERE / "svcomp_tests"
OUT = HERE / "polished_tests" / "cuvee"
OPERATORS = ["forall", "max", "min", "sum"]

TASK = """format_version: '2.0'

# the test {test} of the CAV 2023 paper on MonoCera, converted from svcomp_tests by convert_cuvee.py
input_files: '{name}.c'

properties:
  - property_file: ../../../properties/unreach-call.prp
    expected_verdict: true

options:
  language: C
  data_model: ILP32
"""


def defines(s: str) -> str:
    # as in sv_to_tricera of convert_cav23.py, but by whole words, so that e.g. SIZE does not hit ARRAY_SIZE,
    # and outside the definition, which stays readable as a comment
    for m in re.finditer(r"#define (\w+) (\w+)", s):
        before, after = s.split(m.group(0), 1)
        def substitute(part):
            return re.sub(rf"\b{re.escape(m.group(1))}\b", m.group(2), part)
        s = substitute(before) + "// " + m.group(0) + substitute(after)
    return s


def mallocs(s: str) -> str:
    # as in mallocs_to_arrs of convert_cav23.py: T *a = malloc(n*sizeof(T)); becomes T a[n];
    for m in re.finditer(r"(\w.*)\s+\*(\w+) = malloc\((.*)\);", s):
        size = re.sub(r"sizeof\s*\([^\)]+\)", "1", m.group(3)).replace("1*", "").replace("*1", "")
        s = s.replace(m.group(0), "//" + m.group(0) + "\n\t" + m.group(1) + " " + m.group(2) + "[" + size + "];")
    return s


def convert(test: str):
    source = SVCOMP / f"{test}.c"
    target = OUT / f"{test}.c"
    target.parent.mkdir(parents=True, exist_ok=True)
    header = f"// ./Cuvee.sh -teq -prove benchmarks/monocera/polished_tests/cuvee/{test}.c\n"
    target.write_text(header + mallocs(defines(source.read_text())))
    target.with_suffix(".yml").write_text(TASK.format(test=test, name=target.stem))
    print(target.relative_to(HERE))


def main():
    tests = sys.argv[1:] or [f"{op}/{path.stem}" for op in OPERATORS for path in sorted((SVCOMP / op).glob("*.c"))]
    for test in tests:
        convert(test)


if __name__ == "__main__":
    main()
