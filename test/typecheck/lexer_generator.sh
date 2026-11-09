#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../.."
tmp_dir=$(mktemp -d)
trap 'rm -rf -- "$tmp_dir"' EXIT

cabal exec -- runghc -isrc test/typecheck/LexerGeneratorRegression.hs "$tmp_dir"
for lexer in LegacyLexer CurrentLexer TrailingLexer; do
    cabal exec -- runghc "$tmp_dir/$lexer.hs"
done
