#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${PPAP_BIN:?smoke runner must provide PPAP_BIN}"

tmp_dir=$(mktemp -d)
trap 'rm -rf -- "$tmp_dir"' EXIT

for variant in ALPHA2 BETA; do
    mkdir -p "$tmp_dir/$variant"
    cp "example/$variant/PlanHolLexer.txt" "$tmp_dir/$variant/PlanHolLexer.txt"
    cp "example/$variant/PlanHolParser.txt" "$tmp_dir/$variant/PlanHolParser.txt"

    printf 'LGS\n%s\n\n' "$tmp_dir/$variant/PlanHolLexer.txt" | "$PPAP_BIN" >/dev/null
    printf 'PGS\n%s\n\n' "$tmp_dir/$variant/PlanHolParser.txt" | "$PPAP_BIN" >/dev/null

    cmp "$tmp_dir/$variant/PlanHolLexer.hs" "example/$variant/PlanHolLexer.hs"
    cmp "$tmp_dir/$variant/PlanHolLexer.hs" "src/Hol/$variant/PlanHolLexer.hs"
    cmp "$tmp_dir/$variant/PlanHolParser.hs" "example/$variant/PlanHolParser.hs"
    cmp "$tmp_dir/$variant/PlanHolParser.hs" "src/Hol/$variant/PlanHolParser.hs"
done

echo "generated lexer/parser sources are current"
