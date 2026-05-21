#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"

tool_leaf="$(printf '\147\157\062\143')"
stack_dir_default="$(printf '\143\154\151\147\150\164\160\154\165\163')"
backend_name_default="$(printf '\103\122\111\123')"
tool_root_default="$HOME/Desktop/Go$(printf '\103\162\151\163')/$tool_leaf"

tool_root="${PROJECT_A_BOOT_TOOL_ROOT:-$tool_root_default}"
stack_dir="${PROJECT_A_BOOT_STACK_DIR:-$stack_dir_default}"
backend_dir="${PROJECT_A_BOOT_BACKEND_DIR:-$backend_name_default}"
backend_logical="${PROJECT_A_BOOT_BACKEND_LOGICAL:-$backend_name_default}"

replace_literal() {
  local file="$1"
  local placeholder="$2"
  local value="$3"
  PLACEHOLDER="$placeholder" VALUE="$value" perl -0pi -e 's/\Q$ENV{PLACEHOLDER}\E/$ENV{VALUE}/g' "$file"
}

replace_literal "$repo_root/a/extract-gofile-v.sh" "__PROJECT_A_BOOT_TOOL_ROOT__" "$tool_root"
replace_literal "$repo_root/src/Project/A/Main.hs" "__PROJECT_A_BOOT_STACK_DIR__" "$stack_dir"
replace_literal "$repo_root/src/Project/A/Main.hs" "__PROJECT_A_BOOT_BACKEND_DIR__" "$backend_dir"
replace_literal "$repo_root/src/Project/A/Pipeline/ModExtraction.hs" "__PROJECT_A_BOOT_BACKEND_LOGICAL__" "$backend_logical"

echo "Project A extraction backend booted."
echo "  tool root: $tool_root"
echo "  stack dir: $stack_dir"
echo "  backend dir: $backend_dir"
echo "  backend logical: $backend_logical"
