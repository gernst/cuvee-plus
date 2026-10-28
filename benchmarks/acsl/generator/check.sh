#!/bin/bash
# check all annotated tasks of the given folders, two at a time: results/<folder>.tsv next to this script
# usage: JAR=<cuvee.jar> check.sh <folders>   (JAR defaults to the cuvee.jar of the repository)
G=$(cd "$(dirname "$0")" && pwd)
cd "$G/.."
mkdir -p "$G/results"
for folder in "$@"; do
  ls $folder/*.c $folder/*.i 2>/dev/null | xargs -P 2 -n 1 "$G/check1.sh" > "$G/results/$folder.tsv"
  echo "== $folder: $(cut -f1 "$G/results/$folder.tsv" | sort | uniq -c | tr '\n' ';')"
done
