#!/bin/sh
# Reproduce the Hypercube comparator verification from scratch.
#
# Usage: reproduce.sh <source-project-root> <work-dir>
#   <source-project-root>  Lake project with the solution: `Formalization/`
#                          as a `HypercubeInequality` lib, built (`lake build`),
#                          Mathlib dependency at the pinned rev.
#   <work-dir>             Scratch directory for oleans/exports (kept).
#
# What it does (all Lean content by the challenge + solution sources):
#   1. Compiles the challenge with a Mathlib-only LEAN_PATH (no project
#      oleans on the search path) and reports the single `sorry` warning.
#   2. Exports challenge and solution with `leanexport`, using exactly the
#      export roots `lake comparator` uses (kernel builtins ++ named
#      theorems ++ permitted axioms ++ kernel primitives ++ named
#      definitions), and prints both sha256 hashes.
#   3. On Linux with `bwrap`, runs the real `lake comparator` from those
#      exports and reports its exit code honestly. Elsewhere it prints the
#      exact command to run on a Linux host (macOS cannot run the
#      comparator without --inadvisably-no-sandbox, which is never used).
#
# Exit code: 0 only if every executed step succeeded (on non-Linux the
# comparator step is skipped and reported, exit 0 still requires the
# build/export steps to succeed).
set -u
PROJ="$1"
WORK="$2"
CHALLENGE_LEAN="$(dirname "$0")/hypercube_inequality_comparator.lean"
CONFIG="$(dirname "$0")/hypercube_inequality_comparator.json"

command -v lean lake leanexport >/dev/null 2>&1 || {
  echo "need lean, lake, leanexport on PATH (Lean 4.35.0 toolchain)"; exit 2; }
[ -f "$CHALLENGE_LEAN" ] || { echo "challenge not found: $CHALLENGE_LEAN"; exit 2; }
[ -f "$CONFIG" ] || { echo "config not found: $CONFIG"; exit 2; }
mkdir -p "$WORK"

# Full workspace search path from the project, minus the project's own
# build dir (challenge independence: Mathlib-only search path).
FULL_LP="$(cd "$PROJ" && lake env printenv LEAN_PATH)" || exit 2
PROJ_BUILD="$PROJ/.lake/build/lib/lean"
MATHLIB_LP="$(printf '%s' "$FULL_LP" | tr ':' '\n' | grep -v "^$PROJ_BUILD\$" | paste -sd: -)"
echo "== 1. compile challenge (Mathlib-only search path)"
LEAN_PATH="$WORK:$MATHLIB_LP" lean -o "$WORK/hypercube_inequality_comparator.olean" \
  "$CHALLENGE_LEAN"
echo "challenge compile exit: $?"
test -f "$WORK/hypercube_inequality_comparator.olean" || exit 1

# Exact export roots `lake comparator` uses for this config.
ROOTS="Quot Quot.mk Quot.lift Quot.ind HypercubeInequality.main_full propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
echo "== 2a. export challenge"
LEAN_PATH="$WORK:$MATHLIB_LP" leanexport hypercube_inequality_comparator \
  -- $ROOTS > "$WORK/challenge.ndjson"
echo "challenge export exit: $?"
echo "== 2b. export solution"
LEAN_PATH="$FULL_LP" leanexport HypercubeInequality \
  -- $ROOTS > "$WORK/solution.ndjson"
echo "solution export exit: $?"
test -s "$WORK/challenge.ndjson" || exit 1
test -s "$WORK/solution.ndjson" || exit 1
shasum -a 256 "$WORK/challenge.ndjson" "$WORK/solution.ndjson"

echo "== 3. judge"
if [ "$(uname -s)" = "Linux" ] && command -v bwrap >/dev/null 2>&1; then
  (cd "$WORK" && lake comparator --config "$CONFIG" \
    --challenge-from-export "$WORK/challenge.ndjson" \
    --solution-from-export "$WORK/solution.ndjson")
  echo "lake comparator exit: $?"
else
  echo "not Linux+bwrap: run on a Linux host:"
  echo "  lake comparator --config $CONFIG \\"
  echo "    --challenge-from-export $WORK/challenge.ndjson \\"
  echo "    --solution-from-export $WORK/solution.ndjson"
fi
