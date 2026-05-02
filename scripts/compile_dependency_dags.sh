#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

status=0
for f in papers/*/DependencyDAG.tex; do
  d=$(dirname "$f")
  b=$(basename "$d")
  log="/tmp/dag_compile_${b}.log"
  echo "Compiling $f"
  if (cd "$d" && latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex >"$log" 2>&1); then
    if grep -E "(LaTeX Error|Undefined control sequence|Emergency stop)" "$log" >/dev/null; then
      echo "  WARN: $(grep -m 1 -E "(LaTeX Error|Undefined control sequence|Emergency stop)" "$log")"
      status=1
    else
      echo "  OK"
    fi
    (cd "$d" && latexmk -c DependencyDAG.tex >>"$log" 2>&1)
  else
    echo "  FAIL: see $log"
    status=1
  fi
done

if (( status != 0 )); then
  echo "Dependency DAG compile check finished with issues"
  exit 1
fi

echo "Dependency DAG compile check passed"
