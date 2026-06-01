#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  a/golanggen-translator.sh [options] path/to/gofile.go

Options:
  --golanggen-root=DIR  golanggen checkout.
                        Default: PROJECT_A_GOLANGGEN_ROOT, or the first
                        existing checkout under ~/Desktop/GoCris or ~/Desktop/coq82000.
  -h, --help            Show this help.

The script implements Project A's translator contract: it receives gofile.go as
its last argument and writes only generated Coq to stdout.
EOF
}

if [[ -n "${PROJECT_A_GOLANGGEN_ROOT:-}" ]]; then
  golanggen_root="$PROJECT_A_GOLANGGEN_ROOT"
elif [[ -d "$HOME/Desktop/GoCris/go2c/golanggen" ]]; then
  golanggen_root="$HOME/Desktop/GoCris/go2c/golanggen"
elif [[ -d "$HOME/Desktop/coq82000/go2c/golanggen" ]]; then
  golanggen_root="$HOME/Desktop/coq82000/go2c/golanggen"
else
  golanggen_root="/home/lim/coq82000/go2c/golanggen"
fi
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

# Keep generated declarations on the same Go module path as CGoProgram.
# Coq accepts Go.syntax via Include, but Haskell extraction splits the aliases.
perl -0pi -e 's/Import Go\.syntax\./Import Go./g' "$generated"
perl -0pi -e 's/From go2c Require Import golang_notation expr_sem stmt_sem\./From go2c Require Import golang_notation expr_sem stmt_sem mem./g' "$generated"

perl -0pi -e 's/\bGoUnary_ArithNeg\b/ArithNeg/g; s/\bGoUnary_LogicalNot\b/LogicalNot/g' "$generated"

if grep -Fq 'Definition go_composites : list (Go.ident * StructDecl) := [  ].' "$generated"; then
  perl -0pi -e 's/Lemma ce_well_founded.*?Qed\./Lemma ce_well_founded : well_founded ( \@substr go_composites).\nProof.\n  wf_substr_ce_prooftools.prove_wf_substr_init.\nQed\./s' "$generated"
fi

cat >>"$generated" <<'EOF'

Module ProjectAIO.
  Variant Input : Type :=
    | IntInput (val : Z)
    | BoolInput (val : bool)
    | StringInput (val : String.string).

  Inductive Output : Type :=
    | IntOutput (val : Z)
    | BoolOutput (val : bool)
    | StringOutput (val : String.string)
    | ArrayOutput (elems : list Output)
    | StructOutput (fields : list Output).
End ProjectAIO.

Section ProjectAExtraction.
  Context `{Sigma: GRA}.
  Definition project_a_builtin_args : Type := list (Go.expr * Go.val).
  Definition project_a_mem_cell : Type := C.block * Z.
  Definition project_a_mem_state : Type := list (project_a_mem_cell * Go.val).
  Definition project_a_mem_key : key := ("ProjectA", "mem").
  Definition project_a_next_block_key : key := ("ProjectA", "next_block").
  Definition project_a_same_cell (lhs rhs : project_a_mem_cell) : bool :=
    let '(lhs_block, lhs_ofs) := lhs in
    let '(rhs_block, rhs_ofs) := rhs in
    if Pos.eqb lhs_block rhs_block then Z.eqb lhs_ofs rhs_ofs else false.
  Fixpoint project_a_mem_lookup (cell : project_a_mem_cell) (mem : project_a_mem_state) : option Go.val :=
    match mem with
    | [] => None
    | (cell0, val0) :: rest =>
      if project_a_same_cell cell cell0 then Some val0 else project_a_mem_lookup cell rest
    end.
  Fixpoint project_a_mem_update (cell : project_a_mem_cell) (val : Go.val) (mem : project_a_mem_state) : project_a_mem_state :=
    match mem with
    | [] => [(cell, val)]
    | (cell0, val0) :: rest =>
      if project_a_same_cell cell cell0 then (cell, val) :: rest else (cell0, val0) :: project_a_mem_update cell val rest
    end.
  Fixpoint project_a_mem_copy_range (count : nat) (dst src : project_a_mem_cell) (mem : project_a_mem_state) : project_a_mem_state :=
    match count with
    | O => mem
    | S count' =>
      let '(dst_block, dst_ofs) := dst in
      let '(src_block, src_ofs) := src in
      let val := match project_a_mem_lookup src mem with Some val => val | None => C.Vundef end in
      let mem' := project_a_mem_update dst val mem in
      project_a_mem_copy_range count' (dst_block, (dst_ofs + 1)%Z) (src_block, (src_ofs + 1)%Z) mem'
    end.
  Definition project_a_ptr_cell (ptr : Go.val) : itree crisE project_a_mem_cell :=
    match ptr with
    | C.Vptr blk ofs => Ret (blk, C.Ptrofs.unsigned ofs)
    | _ => triggerUB
    end.
  Definition project_a_mem_size (sz : Go.val) : itree crisE Z :=
    match sz with
    | C.Vint n => Ret (C.Int.unsigned n)
    | C.Vlong n => Ret (C.Int64.unsigned n)
    | _ => triggerUB
    end.
  Definition project_a_malloc_Go (sz : Go.val) : itree crisE Go.val :=
    '_ : Z <- project_a_mem_size sz;;
    next_any <- trigger (SGet project_a_next_block_key);;
    'blk : C.block <- (Any.downcast next_any)?;;
    trigger (SPut project_a_next_block_key (Any.upcast (Pos.succ blk : C.block)));;;
    Ret (C.Vptr blk C.Ptrofs.zero).
  Definition project_a_malloc_C (sz : Go.val) : itree crisE Go.val :=
    project_a_malloc_Go sz.
  Definition project_a_mem_store (args : C.AST.memory_chunk * Go.val * Go.val) : itree crisE unit :=
    let '(_, ptr, val) := args in
    cell <- project_a_ptr_cell ptr;;
    mem_any <- trigger (SGet project_a_mem_key);;
    'mem : project_a_mem_state <- (Any.downcast mem_any)?;;
    trigger (SPut project_a_mem_key (Any.upcast (project_a_mem_update cell val mem))).
  Definition project_a_mem_load (args : C.AST.memory_chunk * Go.val) : itree crisE Go.val :=
    let '(_, ptr) := args in
    cell <- project_a_ptr_cell ptr;;
    mem_any <- trigger (SGet project_a_mem_key);;
    'mem : project_a_mem_state <- (Any.downcast mem_any)?;;
    match project_a_mem_lookup cell mem with
    | Some val => Ret val
    | None => triggerUB
    end.
  Definition project_a_mem_memcpy (args : Z * Go.val * Go.val) : itree crisE unit :=
    let '(size, dst, src) := args in
    src_cell <- project_a_ptr_cell src;;
    dst_cell <- project_a_ptr_cell dst;;
    mem_any <- trigger (SGet project_a_mem_key);;
    'mem : project_a_mem_state <- (Any.downcast mem_any)?;;
    trigger (SPut project_a_mem_key (Any.upcast (project_a_mem_copy_range (Z.to_nat size) dst_cell src_cell mem))).
  Definition project_a_bool_of_val (val : Go.val) : itree crisE bool :=
    match val with
    | C.Vint n => Ret (negb (Z.eqb (C.Int.unsigned n) 0))
    | _ => triggerUB
    end.
  Definition project_a_ascii_of_val (val : Go.val) : itree crisE Ascii.ascii :=
    match val with
    | C.Vint n => Ret (Ascii.ascii_of_nat (Z.to_nat (C.Int.unsigned n)))
    | _ => triggerUB
    end.
  Definition project_a_val_of_ascii (ch : Ascii.ascii) : Go.val :=
    C.Vint (C.Int.repr (Z.of_nat (Ascii.nat_of_ascii ch))).
  Fixpoint project_a_string_chars (str : String.string) : list Ascii.ascii :=
    match str with
    | EmptyString => []
    | String ch rest => ch :: project_a_string_chars rest
    end.
  Definition project_a_uintptr_val (offset : Z) : itree crisE Go.val :=
    AuxiliaryMethods.ZtoVal_uintptr offset.
  Fixpoint project_a_store_string_chars (data : Go.val) (offset : Z) (chars : list Ascii.ascii) : itree crisE unit :=
    match chars with
    | [] => Ret tt
    | ch :: rest =>
      delta <- project_a_uintptr_val offset;;
      '_ : () <- setv main.go_composites Go.types.byte data delta (project_a_val_of_ascii ch);;
      project_a_store_string_chars data (offset + 1)%Z rest
    end.
  Definition project_a_string_to_val (str : String.string) : itree crisE Go.val :=
    let chars := project_a_string_chars str in
    content_size <- project_a_uintptr_val (Z.of_nat (List.length chars));;
    content <- project_a_malloc_Go content_size;;
    '_ : () <- project_a_store_string_chars content 0%Z chars;;
    header_size <- project_a_uintptr_val (Z.of_nat (sizeof main.go_composites Go.types.Tstring));;
    header <- project_a_malloc_Go header_size;;
    zero <- project_a_uintptr_val 0%Z;;
    '_ : () <- setv main.go_composites AuxiliaryMethods.__string_data_type header zero content;;
    len_val <- AuxiliaryMethods.ZtoVal AuxiliaryMethods.__string_len_type (Z.of_nat (List.length chars));;
    len_ofs <- lookup_field_offset main.go_composites Go.types.Tstring AuxiliaryMethods.__string_len;;
    '_ : () <- setv main.go_composites AuxiliaryMethods.__string_len_type header len_ofs len_val;;
    Ret header.
  Fixpoint project_a_read_string_chars (data : Go.val) (offset : Z) (count : nat) : itree crisE String.string :=
    match count with
    | O => Ret EmptyString
    | S count' =>
      delta <- project_a_uintptr_val offset;;
      char_val <- getv main.go_composites Go.types.byte data delta;;
      ch <- project_a_ascii_of_val char_val;;
      rest <- project_a_read_string_chars data (offset + 1)%Z count';;
      Ret (String ch rest)
    end.
  Definition project_a_read_string (val : Go.val) : itree crisE String.string :=
    vi_data_ofs <- lookup_field_offset main.go_composites Go.types.Tstring AuxiliaryMethods.__string_data;;
    vi_len_ofs <- lookup_field_offset main.go_composites Go.types.Tstring AuxiliaryMethods.__string_len;;
    data <- getv main.go_composites Go.types.Tuintptr val vi_data_ofs;;
    len_val <- getv main.go_composites Go.types.int val vi_len_ofs;;
    len_z <- AuxiliaryMethods.ValToZ Go.types.int len_val;;
    project_a_read_string_chars data 0%Z (Z.to_nat len_z).
  Definition project_a_output_of_val (arg : Go.expr * Go.val) : itree crisE ProjectAIO.Output :=
    let '(expr, val) := arg in
    match Go.typeof expr with
    | Go.types.Tint _ _ =>
      z <- AuxiliaryMethods.ValToZ (Go.typeof expr) val;;
      Ret (ProjectAIO.IntOutput z)
    | Go.types.Tbool =>
      b <- project_a_bool_of_val val;;
      Ret (ProjectAIO.BoolOutput b)
    | Go.types.Tstring =>
      str <- project_a_read_string val;;
      Ret (ProjectAIO.StringOutput str)
    | _ => triggerUB
    end.
  Fixpoint project_a_outputs_of_args (args : project_a_builtin_args) : itree crisE (list ProjectAIO.Output) :=
    match args with
    | [] => Ret []
    | arg :: rest =>
      out <- project_a_output_of_val arg;;
      outs <- project_a_outputs_of_args rest;;
      Ret (out :: outs)
    end.
  Definition project_a_scan_request (arg : Go.expr * Go.val) : itree crisE ProjectAIO.Input :=
    match arg with
    | (Eaddrof target _, _) =>
      match Go.typeof target with
      | Go.types.Tint _ _ => Ret (ProjectAIO.IntInput 0)
      | Go.types.Tbool => Ret (ProjectAIO.BoolInput false)
      | Go.types.Tstring => Ret (ProjectAIO.StringInput "")
      | _ => triggerUB
      end
    | _ => triggerUB
    end.
  Fixpoint project_a_scan_requests (args : project_a_builtin_args) : itree crisE (list ProjectAIO.Input) :=
    match args with
    | [] => Ret []
    | arg :: rest =>
      input <- project_a_scan_request arg;;
      inputs <- project_a_scan_requests rest;;
      Ret (input :: inputs)
    end.
  Definition project_a_input_to_val (ty : Go.types.type) (input : ProjectAIO.Input) : itree crisE Go.val :=
    match ty, input with
    | Go.types.Tint _ _, ProjectAIO.IntInput z => AuxiliaryMethods.ZtoVal ty z
    | Go.types.Tbool, ProjectAIO.BoolInput b => Ret (if b then C.Vone else C.Vzero)
    | Go.types.Tstring, ProjectAIO.StringInput str => project_a_string_to_val str
    | _, _ => triggerUB
    end.
  Definition project_a_builtin_print (args : project_a_builtin_args) : itree crisE (list Go.val) :=
    outputs <- project_a_outputs_of_args args;;
    'ignored : Any.t <- trigger (IO "Go.builtin.print" outputs);; Ret ([] : list Go.val).
  Fixpoint project_a_store_scan_values (args : project_a_builtin_args) (inputs : list ProjectAIO.Input) : itree crisE (list Go.val) :=
    match args, inputs with
    | [], [] => Ret ([] : list Go.val)
    | (Eaddrof target _, ptr) :: rest_args, input :: rest_inputs =>
      val <- project_a_input_to_val (Go.typeof target) input;;
      '_ : () <- assign_loc_go main.go_composites (Go.typeof target) ptr val;;
      project_a_store_scan_values rest_args rest_inputs
    | _, _ => triggerUB
    end.
  Definition project_a_builtin_scan (args : project_a_builtin_args) : itree crisE (list Go.val) :=
    requests <- project_a_scan_requests args;;
    'inputs : list ProjectAIO.Input <- trigger (IO "Go.builtin.scan" requests);;
    project_a_store_scan_values args inputs.
  Definition project_a_entry_body (_ : Any.t) : itree crisE Any.t :=
    'rets : list Go.val <- ccallU "main" ([] : list Go.val);;
    match rets with | [] => Ret (Any.upcast tt) | _ :: _ => Ret (Any.upcast false) end.
  Definition project_a_scopes := ["ProjectA"].
  Program Definition project_a_entry_mod : SMod.t := {|
    SMod.scopes := project_a_scopes;
    SMod.fnsems := [
      (None, (false, wmask_all, project_a_scopes, (None, project_a_entry_body)));
      (Some CGoMemName.malloc_Go, (false, wmask_all, project_a_scopes, (None, cfunU project_a_malloc_Go)));
      (Some CGoMemName.malloc_C, (false, wmask_all, project_a_scopes, (None, cfunU project_a_malloc_C)));
      (Some CGoMemName.store, (false, wmask_all, project_a_scopes, (None, cfunU project_a_mem_store)));
      (Some CGoMemName.load, (false, wmask_all, project_a_scopes, (None, cfunU project_a_mem_load)));
      (Some CGoMemName.memcpy, (false, wmask_all, project_a_scopes, (None, cfunU project_a_mem_memcpy)));
      (Some "Go.builtin.print", (false, wmask_all, project_a_scopes, (None, cfunU project_a_builtin_print)));
      (Some "Go.builtin.scan", (false, wmask_all, project_a_scopes, (None, cfunU project_a_builtin_scan)))
    ];
    SMod.initial_st := [
      (project_a_mem_key, Any.upcast ([] : project_a_mem_state));
      (project_a_next_block_key, Any.upcast (1%positive : C.block))
    ]
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  Definition project_a_mod : Mod.t := SMod.to_mod sp_none (SMod.add project_a_entry_mod main.t).
End ProjectAExtraction.
EOF

cat "$generated"
