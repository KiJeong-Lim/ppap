#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"

perl -0pi -e 's/tool_root="\$\{PROJECT_A_TOOL_ROOT:-[^}]*\}"/tool_root="\${PROJECT_A_TOOL_ROOT:-__PROJECT_A_BOOT_TOOL_ROOT__}"/g' \
  "$repo_root/a/extract-gofile-v.sh"

perl -0pi -e 's/tool_root="\$\{PROJECT_A_TOOL_ROOT:-[^}]*\}"/tool_root="\${PROJECT_A_TOOL_ROOT:-__PROJECT_A_BOOT_TOOL_ROOT__}"/g' \
  "$repo_root/a/run.sh"

perl -0pi -e 's/if \[\[ "\$tool_root" == "[^"]*" \]\]; then/if [[ "\$tool_root" == "__PROJECT_A_BOOT_TOOL_ROOT__" ]]; then/g' \
  "$repo_root/a/extract-gofile-v.sh"

perl -0pi -e 's/if \[\[ "\$tool_root" == "[^"]*" \]\]; then/if [[ "\$tool_root" == "__PROJECT_A_BOOT_TOOL_ROOT__" ]]; then/g' \
  "$repo_root/a/run.sh"

perl -0pi -e 's/toolRoot <\/> "[^"]*" <\/> "[^"]*"/toolRoot <\/> "__PROJECT_A_BOOT_STACK_DIR__" <\/> "__PROJECT_A_BOOT_BACKEND_DIR__"/g' \
  "$repo_root/src/Project/A/Main.hs"

perl -0pi -e 's/toolRoot <\/> "[^"]*" <\/> "[^"]*"/toolRoot <\/> "__PROJECT_A_BOOT_STACK_DIR__" <\/> "__PROJECT_A_BOOT_BACKEND_DIR__"/g' \
  "$repo_root/src/Project/A/Pipeline/CoqExtraction.hs"

perl -0pi -e 's/mecBackendLogical = "[^"]*"/mecBackendLogical = "__PROJECT_A_BOOT_BACKEND_LOGICAL__"/g' \
  "$repo_root/src/Project/A/Pipeline/ModExtraction.hs"

echo "Project A extraction backend unbooted."
