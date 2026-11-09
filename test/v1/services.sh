#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
cabal exec -- runghc -w -isrc test/v1/ServiceRegression.hs
