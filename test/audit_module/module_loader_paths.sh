#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH_DIR="$(mktemp -d "$ROOT_DIR/.audit_module_paths.XXXXXX")"
trap 'rm -rf -- "$SCRATCH_DIR"' EXIT
LOCATOR="audit_loader_choice_$$"

cd "$ROOT_DIR"
cabal exec -- runghc -isrc test/audit_module/ModuleLoaderRegression.hs "$ROOT_DIR" "$SCRATCH_DIR" "$LOCATOR"
