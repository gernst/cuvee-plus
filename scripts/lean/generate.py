#!/usr/bin/env python3
# generates lean/TEQ/Database.lean and lean/TEQ/Check.lean from the stable modules of the lemma database (MODULES):
# the definitions as printed by -print lean, each lemma as the proposition Stmt.<name> of its printed statement with
# the premises of lean/premises.txt, and for each lemma the check that the theorem <name> of lean/TEQ/Proofs.lean
# proves it; the datatype of traces is that of lean/TEQ/Semantics.lean, which the printed one must equal
#
#   scripts/lean/generate.py [--jar cuvee.jar] [--check]
#
# --check compares instead of writing and fails if the files differ, e.g. after a change of a module; the lemmas of
# lean/open.txt are removed from the modules before printing

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# the entry of the database and the optional modules that are stable, in the order of the database
MODULES = ["resources/cuvee/teq.dfy", "resources/cuvee/teq/aggregation.dfy", "resources/cuvee/teq/arithmetic.dfy",
           "resources/cuvee/teq/search.dfy", "resources/cuvee/teq/sorted.dfy",
           "resources/cuvee/teq/arrays.dfy", "resources/cuvee/teq/counters.dfy",
           "resources/cuvee/teq/strides.dfy"]

TRACE = """inductive Trace (α₀ : Type) where
  | stop (last : α₀) : Trace α₀
  | step (first : α₀) (rest : Trace α₀) : Trace α₀"""

# functions declared without a body whose meaning is defined in lean/TEQ/Definitions.lean, with their printed types,
# which the generator checks before it drops the printed axiom
DEFINED = {
    "cut": "(Int → Prop) → Int → Int → Int",
    "sorted": "(Int → Int) → Int → Int → Prop",
    "perm": "(Int → Int) → (Int → Int) → Prop",
    "partitioned": "(Int → Int) → Int → Int → Int → Prop",
    "lower": "(Int → Int) → Int → Int → Int",
    "upper": "(Int → Int) → Int → Int → Int",
}


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def run_printer(jar):
    # a private copy of the jar, which a rebuild during the run would otherwise replace
    with tempfile.TemporaryDirectory() as tmp:
        copy = os.path.join(tmp, "cuvee.jar")
        shutil.copy(jar, copy)
        source = os.path.join(tmp, "database.dfy")
        with open(source, "w") as out:
            out.write(modules())
        result = subprocess.run(["java", "-cp", copy, "cuvee.Cuvee", "-print", "lean", source],
                                stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=120)
        if result.returncode != 0 or result.stderr.strip():
            sys.exit("-print lean failed:\n" + result.stderr)
        return result.stdout


# the stable modules concatenated, without the lemmas of lean/open.txt
def modules():
    text = ""
    for module in MODULES:
        with open(os.path.join(ROOT, module)) as f:
            text += f.read() + "\n"
    for name in unproved():
        # the lemma up to the next blank line
        text, n = re.subn(r"^lemma (?:\{[^}]*\} )*" + re.escape(name) + r"\b.*?(?=\n\n|\Z)", "", text, flags=re.S | re.M)
        if n != 1:
            sys.exit("lean/open.txt names " + name + ", which is not a lemma of the database")
    return text


# the functions and constants that the modules declare, whose printed axioms are declarations, not lemmas
def declared(text):
    return set(re.findall(r"^(?:function|const) (?:\{[^}]*\} )*(\w+)", text, re.M))


# the lemmas of lean/open.txt, `name -- why`, which have no proof yet and are left out
def unproved():
    names = []
    with open(os.path.join(ROOT, "lean/open.txt")) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                names.append(line.split(" -- ")[0].strip())
    return names


def premises():
    entries = {}
    with open(os.path.join(ROOT, "lean/premises.txt")) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            name, rest = line.split(":", 1)
            premise = rest.split(" -- ")[0].strip()
            entries.setdefault(name.strip(), []).append(premise)
    return entries


# the binders of a printed lemma, the groups in parentheses and brackets before the colon, and its statement
def split_binders(text):
    i = 0
    binders = []
    while True:
        while i < len(text) and text[i].isspace():
            i += 1
        if i < len(text) and text[i] in "({[":
            depth = 0
            start = i
            while True:
                if text[i] in "({[":
                    depth += 1
                elif text[i] in ")}]":
                    depth -= 1
                i += 1
                if depth == 0:
                    break
            binders.append(norm(text[start:i]))
        else:
            break
    if not text[i:].startswith(":"):
        sys.exit("unexpected lemma: " + text)
    return binders, text[i + 1:].strip()


# the statement and the theorem of a lemma, <name>_rule if a function has the name, which the body of the statement
# Stmt.<name> would otherwise resolve to it
def theorem(name, functions):
    return name + "_rule" if name in functions else name


def generate(printed):
    extra = premises()
    functions = declared(modules())
    blocks = [b for b in printed.strip().split("\n\n") if b.strip()]
    database = []
    lemmas = []
    for block in blocks:
        if block.startswith("inductive Trace"):
            if norm(block) != norm(TRACE):
                sys.exit("the printed datatype of traces differs from that of Semantics.lean:\n" + block)
            continue
        m = re.match(r"(?:@\[simp\] )?axiom (\S+)(.*)", block, re.S)
        # a declared function or constant, whose axiom has no explicit binders, unlike a lemma of the same name
        if m and m.group(1) in functions and not any(b.startswith("(") for b in split_binders(m.group(2))[0]):
            if m.group(1) not in DEFINED:
                database.append(block)
                continue
            if norm(m.group(2)) != ": " + DEFINED[m.group(1)]:
                sys.exit("the printed type of " + m.group(1) + " differs from that of Definitions.lean:\n" + block)
            continue
        if m:
            name = m.group(1)
            binders, statement = split_binders(m.group(2))
            for premise in extra.pop(name, []):
                if premise.startswith("("):
                    binders.append(premise)
                else:
                    statement = premise + " →\n    (" + statement.replace("\n", "\n   ") + ")"
            quantifier = "∀ " + " ".join(binders) + ",\n    " if binders else ""
            statement = statement.replace("\n", "\n  ")
            database.append(f"def Stmt.{theorem(name, functions)} : Prop :=\n  {quantifier}{statement}")
            lemmas.append(theorem(name, functions))
        else:
            database.append(block)
    if extra:
        sys.exit("premises of lemmas that are not in the database: " + ", ".join(extra))

    header = "-- generated by scripts/lean/generate.py with -print lean and the premises of lean/premises.txt from\n" + \
        "".join(f"--   {module}\n" for module in MODULES) + \
        "-- do not edit: a definition that does not check is fixed in the module or in lean.Printer\n"
    database_lean = header + """import TEQ.Definitions

open Classical

set_option linter.unusedVariables false

namespace TEQ

open Nat (zero succ)
open List (nil cons length)

""" + "\n\n".join(database) + "\n\nend TEQ\n"
    check_lean = header + """import TEQ.Proofs

-- each lemma of the database is proved as printed, with the premises of lean/premises.txt, by the theorem of its name
-- (<name>_rule if a function has the name)
namespace TEQ

""" + "\n".join(f"example : Stmt.{name} := @{name}" for name in lemmas) + "\n\nend TEQ\n"
    return database_lean, check_lean


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--jar", default=os.path.join(ROOT, "cuvee.jar"))
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    files = dict(zip(["lean/TEQ/Database.lean", "lean/TEQ/Check.lean"], generate(run_printer(args.jar))))
    stale = []
    for path, text in files.items():
        full = os.path.join(ROOT, path)
        if args.check:
            if not os.path.exists(full) or open(full).read() != text:
                stale.append(path)
        else:
            with open(full, "w") as f:
                f.write(text)
    if stale:
        sys.exit("out of date, run scripts/lean/generate.py: " + ", ".join(stale))


if __name__ == "__main__":
    main()
