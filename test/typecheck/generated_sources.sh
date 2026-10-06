#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${PPAP_BIN:?smoke runner must provide PPAP_BIN}"

tmp_dir=$(mktemp -d)
trap 'rm -rf -- "$tmp_dir"' EXIT

for variant in ALPHA1 ALPHA2 BETA; do
    mkdir -p "$tmp_dir/$variant"
    cp "example/$variant/PlanHolLexer.txt" "$tmp_dir/$variant/PlanHolLexer.txt"
    cp "example/$variant/PlanHolParser.txt" "$tmp_dir/$variant/PlanHolParser.txt"

    printf 'LGS\n%s\n\n' "$tmp_dir/$variant/PlanHolLexer.txt" | "$PPAP_BIN" >/dev/null
    printf 'PGS\n%s\n\n' "$tmp_dir/$variant/PlanHolParser.txt" | "$PPAP_BIN" >/dev/null

    source_dir="src/Hol/$variant"
    if [ "$variant" = ALPHA1 ]; then
        source_dir="$source_dir/Front/Analyzer"
    fi
    cmp "$tmp_dir/$variant/PlanHolLexer.hs" "example/$variant/PlanHolLexer.hs"
    if [ "$variant" = ALPHA1 ]; then
        cmp "$tmp_dir/$variant/PlanHolLexer.hs" "$source_dir/Lexer.hs"
        cmp "$tmp_dir/$variant/PlanHolParser.hs" "$source_dir/Parser.hs"
    else
        cmp "$tmp_dir/$variant/PlanHolLexer.hs" "$source_dir/PlanHolLexer.hs"
        cmp "$tmp_dir/$variant/PlanHolParser.hs" "$source_dir/PlanHolParser.hs"
    fi
    cmp "$tmp_dir/$variant/PlanHolParser.hs" "example/$variant/PlanHolParser.hs"
done

echo "generated lexer/parser sources are current"
