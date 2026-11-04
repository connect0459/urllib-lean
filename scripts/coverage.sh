#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
work=${COVERAGE_DIR:-${TMPDIR:-/tmp}/urllib-lean-coverage}
cc=${LEAN_CC:-clang}

if [ -z "${LLVM_COV:-}" ]; then
  if command -v xcrun >/dev/null 2>&1; then
    LLVM_COV=$(xcrun --find llvm-cov)
    LLVM_PROFDATA=$(xcrun --find llvm-profdata)
  else
    LLVM_COV=$(command -v llvm-cov)
    LLVM_PROFDATA=$(command -v llvm-profdata)
  fi
fi

mkdir -p "$work"
rsync -a --delete --exclude .git --exclude .lake --exclude 'coverage.*' "$root"/ "$work"/

lean_lib=$(lean --print-prefix)/lib
python3 -I - "$work/lakefile.toml" "$lean_lib" <<'PY'
import sys
path, lib = sys.argv[1], sys.argv[2]
text = open(path, encoding="utf-8").read()
head, tail = text.split("[leanOptions]", 1)
flags = (
    'moreLeancArgs = ["-O0", "-fprofile-instr-generate", "-fcoverage-mapping"]\n'
    f'moreLinkArgs = ["-fprofile-instr-generate", "-L{lib}"]\n\n'
)
open(path, "w", encoding="utf-8").write(head.rstrip("\n") + "\n" + flags + "[leanOptions]" + tail)
PY

cd "$work"
LEAN_CC="$cc" lake build coverage
LLVM_PROFILE_FILE="$work/coverage.profraw" .lake/build/bin/coverage
"$LLVM_PROFDATA" merge -sparse coverage.profraw -o coverage.profdata
"$LLVM_COV" export .lake/build/bin/coverage -instr-profile=coverage.profdata > coverage.json
python3 -I "$root/scripts/coverage_report.py" coverage.json "$@"
