#!/bin/sh
# Reproduce the Gaussian Ellipsoid independent-comparator verification.
#
# Usage: reproduce.sh <project-root> <work-dir>
#   <project-root>  Assembled 4.34 Lake project holding the solution as lib
#                   `GaussianEllipsoid` (root `GaussianEllipsoid.lean` plus
#                   `GaussianEllipsoid/` and `GaussianEllipsoidNative/`,
#                   built with the pins in ../Readme.md: Lean v4.34.0-rc2,
#                   mathlib 85e3a25e006c35636f0e53b0e9296caca2685bc0).
#                   See ../Readme.md for the assembly recipe.
#   <work-dir>      Scratch directory for oleans/exports (kept outside git).
#
# Toolchains (explicit; never one ambiguous PATH toolchain for both jobs):
#   LEAN34  4.34 `lean` binary (challenge compile + serializer runs).
#   LAKE34  4.34 `lake` binary (workspace LEAN_PATH resolution).
#   LAKE35  4.35 `lake` binary (official judge; Linux only).
#   LEAN35  4.35 `lean` binary beside LAKE35 (checks the judge's exact build).
#   COMPARATOR_BWRAP  `bwrap` binary for the official judge sandbox.
# Compiler and judge versions AND commit hashes are checked before use.
#
# What it does (all Lean content by the challenge + solution sources):
#   1. Guards: challenge imports are external-only (Mathlib/Lean/Std/
#      Batteries); stage LEAN_PATH is a curated externals whitelist.
#   2. Compiles the challenge with a stage-only LEAN_PATH (dependency
#      oleans only; no project build outputs on the search path) and
#      requires exactly the one authorized `sorry` (theorem placeholder).
#   3. Exports challenge and solution with the 4.34 serializer
#      (Verification/export34.lean), using exactly the export roots
#      `lake comparator` uses for this config (kernel builtins ++ named
#      theorem ++ permitted axioms ++ kernel primitives), and prints both
#      sha256 hashes.
#   4. On Linux with `bwrap`, runs the real official `lake comparator`
#      (4.35) from those exports and reports its exit code honestly.
#      Elsewhere (e.g. macOS) it stops after exporting, prints the exact
#      Linux judge command, and exits 2 — never a passing verdict.
#
# The exports are original-4.34 elaborations serialized to the 4.35 NDJSON
# format (untrusted data); they are never claimed to be a 4.35 source port.
# No 4.34 olean is ever loaded into a 4.35 process.
#
# Exit code: 0 only if guards, compilation, both exports, and the real
# comparator all succeeded. Anything else (including wrong-platform)
# returns nonzero, never a passing verdict.
set -eu
[ "$#" -eq 2 ] || {
  echo "usage: reproduce.sh <project-root> <work-dir>" >&2; exit 2; }
PROJ="$(cd "$1" && pwd)" || exit 2
WORK="$2"
SCRIPT_DIR="$(CDPATH= cd "$(dirname "$0")" && pwd)" || exit 2
CHALLENGE_SRC="$SCRIPT_DIR/gaussian_ellipsoid_comparator.lean"
CONFIG="$SCRIPT_DIR/gaussian_ellipsoid_comparator.json"
SERIALIZER="$SCRIPT_DIR/../Verification/export34.lean"

LEAN34="${LEAN34:-lean}"
LAKE34="${LAKE34:-lake}"
LAKE35="${LAKE35:-lake}"
COMPARATOR_BWRAP="${COMPARATOR_BWRAP:-bwrap}"

GUARDS="$SCRIPT_DIR/guard_inputs.py"
export COMPARATOR_BWRAP

for tool in "$LEAN34" "$LAKE34" shasum python3; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "missing tool: $tool" >&2; exit 2; }
done
[ -f "$CHALLENGE_SRC" ] || { echo "challenge not found: $CHALLENGE_SRC"; exit 2; }
[ -f "$CONFIG" ] || { echo "config not found: $CONFIG"; exit 2; }
[ -f "$SERIALIZER" ] || { echo "serializer not found: $SERIALIZER"; exit 2; }
[ -f "$GUARDS" ] || { echo "input guards not found: $GUARDS"; exit 2; }
mkdir -p "$WORK"
WORK="$(cd "$WORK" && pwd)" || exit 2

echo "== 0. toolchain pins"
# No pipelines here: a failing version command must propagate, even if it
# prints a plausible version before exiting unsuccessfully.
"$LEAN34" --version > "$WORK/toolchain_34.txt"
cat "$WORK/toolchain_34.txt"
grep -q '4\.34\.0-rc2' "$WORK/toolchain_34.txt" || {
  echo "LEAN34 must be Lean 4.34.0-rc2" >&2; exit 2; }
HASH34="$("$LEAN34" --githash)"
[ "$HASH34" = 6a10ac8c22beadecabdbb0919c2b50214762f91d ] || {
  echo "LEAN34 commit does not match the verified toolchain" >&2; exit 2; }
"$LAKE34" --version > "$WORK/lake_34.txt"
grep -q 'Lean version 4\.34\.0-rc2' "$WORK/lake_34.txt" || {
  echo "LAKE34 must be from the same Lean 4.34.0-rc2 toolchain" >&2; exit 2; }
if [ "$(uname -s)" = "Linux" ]; then
  command -v "$LAKE35" >/dev/null 2>&1 || {
    echo "missing tool: $LAKE35" >&2; exit 2; }
  command -v "$COMPARATOR_BWRAP" >/dev/null 2>&1 || {
    echo "missing tool: $COMPARATOR_BWRAP" >&2; exit 2; }
  LAKE35_EXE="$(command -v "$LAKE35")"
  LEAN35="${LEAN35:-$(dirname "$LAKE35_EXE")/lean}"
  command -v "$LEAN35" >/dev/null 2>&1 || {
    echo "missing tool: $LEAN35" >&2; exit 2; }
  "$LAKE35" --version > "$WORK/toolchain_35.txt"
  cat "$WORK/toolchain_35.txt"
  grep -q 'Lean version 4\.35\.0' "$WORK/toolchain_35.txt" || {
    echo "LAKE35 must be Lean 4.35.0" >&2; exit 2; }
  HASH35="$("$LEAN35" --githash)"
  [ "$HASH35" = eb6cafb7290e8bd5f2937522d8d804f58f02bafc ] || {
    echo "LEAN35 commit does not match the official judge" >&2; exit 2; }
fi

echo "== 0b. challenge import and configuration guards"
python3 "$GUARDS" challenge "$CHALLENGE_SRC" "$CONFIG"

# Curated paths come from the exact nine external dependencies in the pinned
# manifest. No solution outputs, foreign checkouts, unlisted packages, or
# relative/empty search-path entries are accepted for the challenge.
FULL_LP="$(cd "$PROJ" && "$LAKE34" env printenv LEAN_PATH)" || exit 2
printf '%s\n' "$FULL_LP" > "$WORK/full_lean_path.txt"
python3 "$GUARDS" paths "$PROJ" "$WORK/full_lean_path.txt" "$WORK/external_lean_path.txt"
MATHLIB_LP="$(cat "$WORK/external_lean_path.txt")"

echo "== 1. compile challenge (externals-only search path)"
cp "$CHALLENGE_SRC" "$WORK/gaussian_ellipsoid_comparator.lean"
(cd "$WORK" && LEAN_PATH="$WORK:$MATHLIB_LP" "$LEAN34" \
  -o "$WORK/gaussian_ellipsoid_comparator.olean" \
  gaussian_ellipsoid_comparator.lean) > "$WORK/challenge_build.log" 2>&1
echo "challenge compile exit: $?"
test -f "$WORK/gaussian_ellipsoid_comparator.olean" || exit 1
SORRY_COUNT="$(grep -c 'declaration uses .sorry.' "$WORK/challenge_build.log" || true)"
[ "$SORRY_COUNT" = "1" ] || {
  echo "expected exactly one authorized sorry, found: $SORRY_COUNT" >&2; exit 1; }

# Exact export roots `lake comparator` uses for this config:
# builtinTargets ++ theoremNames ++ legalAxioms ++ primitiveTargets
# (++ definitionNames, empty here by design: fixed definitions, not holes).
ROOTS="Quot Quot.mk Quot.lift Quot.ind GaussianEllipsoid.strict_threshold_unconditional propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
echo "== 2a. export challenge (4.34 serializer)"
LEAN_PATH="$WORK:$MATHLIB_LP" "$LEAN34" --run "$SERIALIZER" \
  gaussian_ellipsoid_comparator -- $ROOTS > "$WORK/challenge.ndjson" 2>"$WORK/challenge_export.log"
echo "challenge export exit: $?"
echo "== 2b. export solution (4.34 serializer)"
LEAN_PATH="$FULL_LP" "$LEAN34" --run "$SERIALIZER" \
  GaussianEllipsoid -- $ROOTS > "$WORK/solution.ndjson" 2>"$WORK/solution_export.log"
echo "solution export exit: $?"
test -s "$WORK/challenge.ndjson" || exit 1
test -s "$WORK/solution.ndjson" || exit 1
shasum -a 256 "$WORK/challenge.ndjson" "$WORK/solution.ndjson"

echo "== 3. judge"
if [ "$(uname -s)" = "Linux" ]; then
  (cd "$WORK" && PATH="$(dirname "$LAKE35_EXE"):$PATH" "$LAKE35" comparator --config "$CONFIG" \
    --challenge-from-export "$WORK/challenge.ndjson" \
    --solution-from-export "$WORK/solution.ndjson")
  echo "lake comparator exit: $?"
else
  echo "exports complete; the official judge needs Linux+bwrap, so it was NOT run here."
  echo "On a Linux host with the 4.35 toolchain, run:"
  echo "  COMPARATOR_BWRAP=<bwrap> <4.35-toolchain>/bin/lake comparator \\"
  echo "    --config $CONFIG \\"
  echo "    --challenge-from-export $WORK/challenge.ndjson \\"
  echo "    --solution-from-export $WORK/solution.ndjson"
  echo "No passing verification verdict without that run." >&2
  exit 2
fi
