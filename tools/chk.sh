#!/bin/bash
# Check the session against the prebuilt HOL-Higher_Diff heap (Isabelle2025-2; it has no `process` tool).
# usage: tools/chk.sh [TIMEOUT]   -- prints EXIT code and the *** error lines
D=$(cd "$(dirname "$0")/.." && pwd); TO=${1:-600}
ISA=$HOME/Desktop/Isabelle/Isabelle2025-2/bin/isabelle
LOG=$D/tools/build.log
cd "$D"
timeout "$TO" "$ISA" build -d "$HOME/Desktop/Higher_Diff" -d "$HOME/Desktop/Isabelle/afp_extra/Projected_Gradient_Descent" -d . Logistic_Regression > "$LOG" 2>&1
RC=$?
echo "EXIT $RC"
grep -nE '^\*\*\*|^Timing|Finished|FAILED' "$LOG" | head -80
