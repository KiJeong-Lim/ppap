#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  a/golanggen-translator.sh [options] path/to/gofile.go

Options:
  --golanggen-root=DIR  golanggen checkout.
                        Default: PROJECT_A_GOLANGGEN_ROOT or /home/lim/coq82000/go2c/golanggen
  -h, --help            Show this help.

The script implements Project A's translator contract: it receives gofile.go as
its last argument and writes only generated Coq to stdout.
EOF
}

golanggen_root="${PROJECT_A_GOLANGGEN_ROOT:-/home/lim/coq82000/go2c/golanggen}"
gofile=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --golanggen-root=*)
      golanggen_root="${1#*=}"
      shift
      ;;
    --golanggen-root)
      golanggen_root="${2:?missing value for --golanggen-root}"
      shift 2
      ;;
    --*)
      echo "error: unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      if [[ -n "$gofile" ]]; then
        echo "error: only one gofile.go may be provided" >&2
        usage >&2
        exit 2
      fi
      gofile="$1"
      shift
      ;;
  esac
done

if [[ -z "$gofile" ]]; then
  echo "error: missing path/to/gofile.go" >&2
  usage >&2
  exit 2
fi

if [[ ! -f "$gofile" ]]; then
  echo "error: input file does not exist: $gofile" >&2
  exit 2
fi

if [[ ! -d "$golanggen_root" ]]; then
  echo "error: golanggen root does not exist: $golanggen_root" >&2
  exit 2
fi

tmpdir="$(mktemp -d)"
cleanup() {
  rm -rf "$tmpdir"
}
trap cleanup EXIT

cp "$gofile" "$tmpdir/gofile.go"

if ! (cd "$golanggen_root" && go run ./cmd/golanggen --gofile "$tmpdir/gofile.go") >"$tmpdir/golanggen.stdout" 2>"$tmpdir/golanggen.stderr"; then
  cat "$tmpdir/golanggen.stdout" >&2
  cat "$tmpdir/golanggen.stderr" >&2
  exit 1
fi

generated="$tmpdir/main.v"
if [[ ! -f "$generated" ]]; then
  echo "error: expected generated Coq file does not exist: $generated" >&2
  cat "$tmpdir/golanggen.stdout" >&2
  cat "$tmpdir/golanggen.stderr" >&2
  exit 1
fi

perl -0pi -e 's/Σ/Sigma/g' "$generated"

if grep -Fq 'Definition go_composites : list (Go.ident * StructDecl) := [  ].' "$generated"; then
  perl -0pi -e 's/Lemma ce_well_founded.*?Qed\./Lemma ce_well_founded : well_founded ( \@substr go_composites).\nProof.\n  wf_substr_ce_prooftools.prove_wf_substr_init.\nQed\./s' "$generated"
fi

cat >>"$generated" <<'EOF'

Section ProjectAExtraction.
  Context `{Sigma: GRA}.
  Definition project_a_mod : Mod.t := SMod.to_mod sp_none main.t.
End ProjectAExtraction.
EOF

cat "$generated"
