#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${PPAP_BIN:?smoke runner must provide PPAP_BIN}"

tmp_dir=$(mktemp -d)
trap 'rm -rf -- "$tmp_dir"' EXIT

write_spec() {
    local path=$1
    local rhs=$2
    local action=$3
    cat >"$path" <<'EOF'
\hshead {
    module Main where
}

\target {
    token-type: "Token"
    parser-name: "parse"
    result-type: "Int"
    start: $Start
    terminals:
        "Tok value": $token 0 none
}

\define $Start : "Int" {
EOF
    printf '    10 [%s]:\n%s\n}\n' "$rhs" "$action" >>"$path"
    cat >>"$path" <<'EOF'

\define $Atom : "Int" {
    10 [$token]:
        $1.value
}

\hstail {
    data Token = Tok Int deriving (Eq, Show)
    main = case (parse [Tok 7], parse [], parse [Tok 7, Tok 8]) of
        (Right 7, Left Nothing, Left (Just (Tok 8))) -> return ()
        actual -> error (show actual)
}
EOF
}

generate() {
    printf 'PGS\n%s\n' "$1" | "$PPAP_BIN" >"$1.log" 2>&1
}

check_parser() {
    generate "$1"
    test ! -f "${1%.txt}.failed"
    cabal exec -- runghc -w "${1%.txt}.hs"
}

write_spec "$tmp_dir/hygiene.txt" '$Wrap ($Box $Atom)' '        $1'
cat >>"$tmp_dir/hygiene.txt" <<'EOF'

\define $Wrap ($Atom : "Int") : "Int" {
    10 [$Atom]:
        $1
}

\define $Box ($X : "Int") : "Int" {
    10 [$X]:
        $1
}
EOF
check_parser "$tmp_dir/hygiene.txt"
sed -e 's/\$Wrap (\$Atom/\$Wrap (\$Param/' -e 's/10 \[\$Atom\]/10 [\$Param]/' "$tmp_dir/hygiene.txt" >"$tmp_dir/renamed.txt"
check_parser "$tmp_dir/renamed.txt"

write_spec "$tmp_dir/multiline.txt" '$Atom' '        let value = $1
            offset = 1
        in case value of
            7 -> value + offset - 1
            _ -> 0'
check_parser "$tmp_dir/multiline.txt"

write_spec "$tmp_dir/multiline-do.txt" '$Atom' '        maybe 0 id $ do value <- Just $1
                        offset <- Just 1
                        return (value + offset - 1)'
check_parser "$tmp_dir/multiline-do.txt"

for kind in nonterminal terminal; do
    for index in -1 0 2; do
        rhs='$Atom'
        suffix=''
        if [ "$kind" = terminal ]; then
            rhs='$token'
            suffix='.value'
        fi
        spec="$tmp_dir/$kind-$index.txt"
        write_spec "$spec" "$rhs" "        \$$index$suffix"
        generate "$spec"
        test ! -f "${spec%.txt}.hs"
        grep -F "the index $index is outside the rhs range 1..1." "${spec%.txt}.failed" >/dev/null
        grep -F 'generating-failed' "$spec.log" >/dev/null
    done
done

echo 'PGS scheme substitution, multiline actions, and action index regressions passed'
