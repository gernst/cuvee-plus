#!/usr/bin/env python3
"""The archive of Cuvée for SV-COMP, packaged and uploaded to Zenodo.

  python3 scripts/zenodo.py package             builds dist/cuvee.zip from the last commit and runs its smoke test
  python3 scripts/zenodo.py upload [--sandbox]  uploads it to a draft of a Zenodo record, which is not published

The draft is checked and published by hand on the website of Zenodo, which cannot be undone and gives the DOI of the
version, for fm-tools (data/cuvee.yml) and the paper.

The archive has a single root directory cuvee/ with the executable Cuvee.sh, cuvee.jar, z3, the licenses, and the
files of the folder archive/: the README of the archive, smoketest.sh, and its examples, as SV-COMP requires
(https://sv-comp.sosy-lab.org/2027/submission.php) and fm-tools checks (ci/check_archive.py); no sources, no tool-info
module, which goes to BenchExec. Java 21 is not included, the entry of fm-tools (data/cuvee.yml) requires the package
openjdk-21-jre-headless instead.

The first upload creates a record; a later one replaces the file of the draft if it has not been published yet, and
otherwise creates a new version of the record, such that all versions share one concept DOI; fm-tools takes the DOI of
a version, whose record contains a single zip file. The id of the last record is kept in scripts/zenodo.json
(scripts/zenodo-sandbox.json for the sandbox), which is public information.

The token of Zenodo, a personal access token with the scopes deposit:write and deposit:actions (Account,
Applications, Personal access tokens), is read from the environment variable ZENODO_TOKEN or from the file
~/.config/zenodo/token; for the sandbox (https://sandbox.zenodo.org, a separate account) from ZENODO_SANDBOX_TOKEN or
~/.config/zenodo/sandbox-token. It is never printed.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).parent.parent
DIST = ROOT / "dist"
ARCHIVE = DIST / "cuvee.zip"

# the files of the archive from the repository, where cuvee.jar is the fresh assembly (see package), and those
# written for the archive in the folder archive/, which are copied as they are
FILES = ["Cuvee.sh", "z3", "LICENSE", "LICENSE.z3", "LICENSE.scala", "LICENSE.sourcecode", "LICENSE.snakeyaml"]
EXTRA = ROOT / "archive"

# the executables of the archive, which BenchExec and the CI of SV-COMP run
EXECUTABLES = ["Cuvee.sh", "z3", "smoketest.sh"]

INSTANCES = {
    False: ("https://zenodo.org/api", "ZENODO_TOKEN", "token", "zenodo.json"),
    True: ("https://sandbox.zenodo.org/api", "ZENODO_SANDBOX_TOKEN", "sandbox-token", "zenodo-sandbox.json"),
}

METADATA = {
    "title": "Cuvée: Loop Summaries by Trace Equation Systems and a Lemma Database",
    "upload_type": "software",
    "description": "<p>Cuvée is a multi-language and multi-technique verification tool. It supports C, Dafny, Boogie, "
                   "and SV-LIB among its frontends and backends. Verification conditions can be generated from "
                   "existing annotations or inferred by automatic methods, including Constrained Horn Solvers and "
                   "Trace Equation Systems.</p>"
                   "<p>This archive contains the SV-COMP contribution for participation in the C track (Arrays, Loops) "
                   "and the SV-LIB track.</p>",
    "creators": [
        {"name": "Ernst, Gidon", "affiliation": "Ludwig Maximilian University of Munich", "orcid": "0000-0002-3289-5764"}
    ],
    "copyright": "Copyright (C) 2026 Gidon Ernst",
    "license": "apache-2.0",
    "access_right": "open",
    "related_identifiers": [
        {"identifier": "https://github.com/gernst/cuvee-plus", "relation": "isSupplementTo", "resource_type": "software"}
    ],
    # the repository URL and programming language of the form (Software)
    "custom": {
        "code:codeRepository": "https://github.com/gernst/cuvee-plus",
        "code:programmingLanguage": [{"id": "scala"}],
    },
}


def run(cmd: list[str], cwd: Path = ROOT, timeout: int = 600) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=timeout)


def package():
    # the assembly and the files of the archive from the last commit, in a temporary checkout of it, such that
    # uncommitted changes of the working tree, e.g. of others working on it, are never included; z3 is not under
    # version control and comes from the working tree
    commit = run(["git", "rev-parse", "--short", "HEAD"]).stdout.strip()
    status = run(["git", "status", "--porcelain", "--untracked-files=no"]).stdout.strip()
    if status:
        print("note: uncommitted changes, which the archive does not include:\n" + status, file=sys.stderr)

    folder = DIST / "cuvee"
    shutil.rmtree(folder, ignore_errors=True)
    folder.mkdir(parents=True)

    with tempfile.TemporaryDirectory(prefix="cuvee-build-") as tmp:
        checkout = Path(tmp) / "cuvee-plus"
        added = run(["git", "worktree", "add", "--detach", str(checkout), commit])
        if added.returncode != 0:
            sys.exit("git worktree add failed:\n" + added.stderr)
        try:
            build = run(["mill", "-i", "assembly"], cwd=checkout, timeout=1800)
            if build.returncode != 0:
                sys.exit("mill assembly failed:\n" + build.stdout + build.stderr)

            shutil.copy2(checkout / "out" / "assembly.dest" / "out.jar", folder / "cuvee.jar")
            for name in FILES:
                shutil.copy2(ROOT / name if name == "z3" else checkout / name, folder / name)
            shutil.copytree(checkout / EXTRA.name, folder, dirs_exist_ok=True)
        finally:
            run(["git", "worktree", "remove", "--force", str(checkout)])
    for name in EXECUTABLES:
        (folder / name).chmod(0o755)

    # zip keeps the executable bits of Cuvee.sh and z3, which BenchExec needs
    ARCHIVE.unlink(missing_ok=True)
    zipped = run(["zip", "-q", "-r", ARCHIVE.name, "cuvee"], cwd=DIST)
    if zipped.returncode != 0:
        sys.exit("zip failed:\n" + zipped.stderr)
    print(f"{ARCHIVE.relative_to(ROOT)}: {ARCHIVE.stat().st_size / 2**20:.1f} MB, from commit {commit}")

    smoke()


# the smoke test of the archive (archive/smoketest.sh), unpacked into a temporary directory, as the CI of SV-COMP
# runs it, which checks the version, the bundled z3, and the expected results of its examples
def smoke():
    with tempfile.TemporaryDirectory(prefix="cuvee-zip-") as tmp:
        unzipped = run(["unzip", "-q", str(ARCHIVE), "-d", tmp])
        if unzipped.returncode != 0:
            sys.exit("unzip failed:\n" + unzipped.stderr)

        test = run(["./smoketest.sh"], cwd=Path(tmp) / "cuvee", timeout=300)
        print(test.stdout + test.stderr, end="")
        if test.returncode != 0:
            sys.exit("smoketest.sh failed")


def token(sandbox: bool) -> str:
    _, variable, file, _ = INSTANCES[sandbox]
    path = Path.home() / ".config" / "zenodo" / file
    value = os.environ.get(variable) or (path.read_text().strip() if path.exists() else "")
    if not value:
        sys.exit(f"no token: set {variable} or write it to {path}")
    return value


def request(sandbox: bool, method: str, url: str, body: bytes | None = None, content: str = "application/json"):
    base = INSTANCES[sandbox][0]
    headers = {"Authorization": "Bearer " + token(sandbox), "Accept": "application/json"}
    if body is not None:
        headers["Content-Type"] = content
    req = urllib.request.Request(url if url.startswith("http") else base + url, data=body, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=600) as response:
            data = response.read()
            return json.loads(data) if data else None
    except urllib.error.HTTPError as e:
        sys.exit(f"{method} {req.full_url}: {e.code} {e.read().decode(errors='replace')}")


def state_file(sandbox: bool) -> Path:
    return ROOT / "scripts" / INSTANCES[sandbox][3]


def load_state(sandbox: bool) -> dict:
    path = state_file(sandbox)
    return json.loads(path.read_text()) if path.exists() else {}


def save_state(sandbox: bool, state: dict):
    state_file(sandbox).write_text(json.dumps(state, indent=2) + "\n")


# the version of the packaged tool, as its -version prints it (Cuvée 0.41.4), which is the version of the record
def version() -> str:
    printed = run(["java", "-cp", str(DIST / "cuvee" / "cuvee.jar"), "cuvee.Cuvee", "-version"], timeout=60).stdout
    match = re.match(r"Cuvée (\S+)", printed)
    if not match:
        sys.exit("no version of the packaged tool: " + printed)
    return match.group(1)


def upload(sandbox: bool):
    if not ARCHIVE.exists():
        sys.exit(f"{ARCHIVE.relative_to(ROOT)} is missing, run package first")
    metadata = METADATA | {"version": version()}

    state = load_state(sandbox)
    last = request(sandbox, "GET", f"/deposit/depositions/{state['id']}") if state else None
    if last is None:
        # the first record
        draft = request(sandbox, "POST", "/deposit/depositions", b"{}")
    elif not last.get("submitted"):
        # the draft of an earlier upload, not published yet, which is replaced
        draft = last
    else:
        # the last record has been published on the website: a new version of it, which starts with its files and
        # metadata
        created = request(sandbox, "POST", f"/deposit/depositions/{state['id']}/actions/newversion")
        draft = request(sandbox, "GET", created["links"]["latest_draft"])

    # a single zip file per record
    for file in draft.get("files", []):
        request(sandbox, "DELETE", file["links"]["self"])

    data = ARCHIVE.read_bytes()
    uploaded = request(sandbox, "PUT", f"{draft['links']['bucket']}/{ARCHIVE.name}", data, "application/octet-stream")
    md5 = hashlib.md5(data).hexdigest()
    if uploaded.get("checksum") != "md5:" + md5:
        sys.exit(f"checksum mismatch: {uploaded.get('checksum')} uploaded, md5:{md5} local")

    request(sandbox, "PUT", f"/deposit/depositions/{draft['id']}", json.dumps({"metadata": metadata}).encode())
    save_state(sandbox, {"id": draft["id"]})
    print("draft:", draft["links"]["html"])
    print("check it there and publish it on the website, which gives the DOI of this version")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=["package", "upload"])
    parser.add_argument("--sandbox", action="store_true", help="use https://sandbox.zenodo.org, for trying it out")
    args = parser.parse_args()

    if args.command == "package":
        package()
    else:
        upload(args.sandbox)
