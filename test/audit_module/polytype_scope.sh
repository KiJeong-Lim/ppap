#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."
cabal exec -- runghc -isrc test/audit_module/polytype_scope.hs
