#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

workdir=".project-a-test-work"

rm -rf "$workdir"

cabal build

printf 'Project --one --seed=1 --size=0 --workdir=.project-a-test-work\n\n' \
  | env -u PROJECT_A_TRANSLATOR cabal run -v0 ppap

test -f "$workdir/cases/000001/gofile.go"
test -f "$workdir/cases/000001/result.json"
test -f "$workdir/cases/000001/native/build.log"

printf 'Project --fuzz --cases=3 --seed=10 --size=3 --workdir=.project-a-test-work\n\n' \
  | env -u PROJECT_A_TRANSLATOR cabal run -v0 ppap

test -f "$workdir/cases/000003/result.json"
