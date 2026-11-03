#!/bin/sh
# Reproduce the Alpha-Cycle independent-comparator verification.
#
# Usage: reproduce.sh <package-root> <work-dir>
#   <package-root>  AlphaCycle package holding `Formalization/` (45 Lean
#                   modules, root `AlphaCycle.lean`), `Comparator/` (the
#                   independent challenge) and `Verification/` (build/export
#                   utilities), as checked into
#                   `Formalized Publications/Papers/AlphaCycle`.
#   <work-dir>      Scratch directory for build outputs and exports
#                   (kept outside git).
#
# Environment:
#   LEAN34              4.34 `lean` binary (challenge/solution builds,
#                       challenge compile, serializer runs). Default: lean.
#   EXTERNALS_LEAN_PATH Colon-separated pinned external dependency outputs
#                       (Mathlib at 85e3a25e006c35636f0e53b0e9296caca2685bc0
#                       plus its eight pinned companion packages; the package
#                       Readme gives the assembly recipe). Required.
#   LAKE35              4.35 `lake` binary (official judge; Linux only).
#   LEAN35              4.35 `lean` binary beside LAKE35 (checks the judge's
#                       exact build). Default: <dir of LAKE35>/lean.
#   COMPARATOR_BWRAP    `bwrap` binary for the official judge sandbox.
#
# Compiler and judge versions AND commit hashes are checked before use.
# A failing version command (even one that prints a plausible version first)
# fails the run: no pipelines hide exit codes.
#
# What it does (all Lean content by the challenge + solution sources):
#   0. Toolchain pin guards + challenge/source/path hygiene guards.
#   1. Builds the solution from the package sources (direct-Lean topological
#      order, fresh process per file) and requires zero `sorry`.
#   2. Builds the challenge the same way (externals-only search path) and
#      requires exactly the one authorized `sorry` (theorem placeholder).
#   3. Exports challenge and solution with the 4.34 serializer
#      (Verification/export34.lean), using exactly the export roots
#      `lake comparator` uses for this config; each export must be complete
#      (every root resolves, no refusal) and deterministic (two challenge
#      runs are byte-identical). Prints both sha256 hashes.
#   4. On Linux with `bwrap`, runs the real official `lake comparator`
#      (4.35) from those exports and reports its exit code honestly.
#      Elsewhere (e.g. macOS) it stops after exporting, prints the exact
#      Linux judge command, and exits 2 — never a passing verdict.
#
# The exports are original-4.34 elaborations serialized to the 4.35 NDJSON
# format (untrusted data); they are never claimed to be a 4.35 source port.
# No 4.34 olean is ever loaded into a 4.35 process.
#
# Exit code: 0 only if guards, both builds, both exports, and the real
# comparator all succeeded. Anything else (including wrong-platform)
# returns nonzero, never a passing verdict.
set -eu
[ "$#" -eq 2 ] || {
  echo "usage: reproduce.sh <package-root> <work-dir>" >&2; exit 2; }
PKG="$(cd "$1" && pwd)" || exit 2
WORK="$2"
SCRIPT_DIR="$(CDPATH= cd "$(dirname "$0")" && pwd)" || exit 2
CHALLENGE_DIR="$SCRIPT_DIR"
CONFIG="$SCRIPT_DIR/alpha_cycle_comparator.json"
SERIALIZER="$SCRIPT_DIR/../Verification/export34.lean"
BUILD_SOLUTION="$SCRIPT_DIR/../Verification/build_solution.sh"
BUILD_CHALLENGE="$SCRIPT_DIR/../Verification/build_challenge.sh"
CHECK_EXPORTS="$SCRIPT_DIR/../Verification/check_exports.py"
GUARDS="$SCRIPT_DIR/guard_inputs.py"

LEAN34="${LEAN34:-lean}"
LAKE35="${LAKE35:-lake}"
COMPARATOR_BWRAP="${COMPARATOR_BWRAP:-bwrap}"
export COMPARATOR_BWRAP

for tool in "$LEAN34" python3; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "missing tool: $tool" >&2; exit 2; }
done
if ! command -v shasum >/dev/null 2>&1 && \
   ! command -v sha256sum >/dev/null 2>&1; then
  echo "missing tool: shasum or sha256sum" >&2; exit 2; fi
[ -f "$CONFIG" ] || { echo "config not found: $CONFIG" >&2; exit 2; }
[ -f "$SERIALIZER" ] || { echo "serializer not found: $SERIALIZER" >&2; exit 2; }
[ -f "$GUARDS" ] || { echo "input guards not found: $GUARDS" >&2; exit 2; }
[ -n "${EXTERNALS_LEAN_PATH:-}" ] || {
  echo "EXTERNALS_LEAN_PATH is not set (pinned external dependency outputs)" >&2
  exit 2; }
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

echo "== 0b. challenge and path guards"
python3 "$GUARDS" challenge "$CHALLENGE_DIR" "$CONFIG"
printf '%s' "$EXTERNALS_LEAN_PATH" > "$WORK/externals_raw.txt"
python3 "$GUARDS" paths "$PKG" "$WORK/externals_raw.txt" \
  "$WORK/solution_build" "$WORK/challenge_build" "$WORK/externals.txt"
MATHLIB_LP="$(cat "$WORK/externals.txt")"
export EXTERNALS_LEAN_PATH="$MATHLIB_LP"

echo "== 1. build solution from package sources (must be sorry-free)"
python3 "$GUARDS" solution "$PKG"
LEAN34="$LEAN34" sh "$BUILD_SOLUTION" "$PKG/Formalization" \
  "$WORK/solution_build" > "$WORK/solution_build.log" 2>&1
echo "solution build exit: $?"
if grep -i 'uses `sorry`' "$WORK/solution_build.log"; then
  echo "solution build has a sorry warning" >&2; exit 1; fi

echo "== 2. build challenge (externals-only search path)"
LEAN34="$LEAN34" sh "$BUILD_CHALLENGE" "$CHALLENGE_DIR" \
  "$WORK/challenge_build" > "$WORK/challenge_build.log" 2>&1
echo "challenge build exit: $?"
SORRY_COUNT="$(grep -c 'declaration uses .sorry.' \
  "$WORK/challenge_build.log" || true)"
[ "$SORRY_COUNT" = "1" ] || {
  echo "expected exactly one authorized sorry, found: $SORRY_COUNT" >&2
  exit 1; }

# Exact export roots `lake comparator` uses for this config:
# builtinTargets ++ theoremNames ++ legalAxioms ++ primitiveTargets
# (++ definitionNames, empty here by design: fixed definitions, not holes).
ROOTS="Quot Quot.mk Quot.lift Quot.ind AlphaCycle.PaperHypergraph.paper_sharp_classification propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
echo "== 3a. export challenge (4.34 serializer)"
# NOTE: Lean 4.34.0-rc2 `lean --run` exits 133 on some hosts (including this
# Mac) after producing complete output, so the run below is NOT gated on its
# exit code. Completeness is enforced instead: the NDJSON must be non-empty,
# every requested root must resolve in it, its log must show no refusal, and
# a second run must be byte-identical (determinism).
LEAN_PATH="$WORK/challenge_build:$MATHLIB_LP" "$LEAN34" --run "$SERIALIZER" \
  alpha_cycle_comparator -- $ROOTS > "$WORK/challenge.ndjson" \
  2>"$WORK/challenge_export.log" || true
test -s "$WORK/challenge.ndjson" || {
  echo "challenge export is empty" >&2; exit 1; }
if grep -q "REFUSED\|uncaught exception" "$WORK/challenge_export.log"; then
  echo "challenge export refused" >&2; exit 1; fi
python3 "$CHECK_EXPORTS" "$WORK/challenge.ndjson" $ROOTS || exit 1
LEAN_PATH="$WORK/challenge_build:$MATHLIB_LP" "$LEAN34" --run "$SERIALIZER" \
  alpha_cycle_comparator -- $ROOTS > "$WORK/challenge_again.ndjson" \
  2>"$WORK/challenge_export_again.log" || true
cmp "$WORK/challenge.ndjson" "$WORK/challenge_again.ndjson" || {
  echo "challenge export is not deterministic" >&2; exit 1; }
echo "challenge export: complete and deterministic"
echo "== 3b. export solution (4.34 serializer)"
LEAN_PATH="$WORK/solution_build:$MATHLIB_LP" "$LEAN34" --run "$SERIALIZER" \
  AlphaCycle -- $ROOTS > "$WORK/solution.ndjson" \
  2>"$WORK/solution_export.log" || true
test -s "$WORK/solution.ndjson" || {
  echo "solution export is empty" >&2; exit 1; }
if grep -q "REFUSED\|uncaught exception" "$WORK/solution_export.log"; then
  echo "solution export refused" >&2; exit 1; fi
python3 "$CHECK_EXPORTS" "$WORK/solution.ndjson" $ROOTS || exit 1
if command -v shasum >/dev/null 2>&1; then
  shasum -a 256 "$WORK/challenge.ndjson" "$WORK/solution.ndjson"
else
  sha256sum "$WORK/challenge.ndjson" "$WORK/solution.ndjson"
fi

echo "== 4. judge"
if [ "$(uname -s)" = "Linux" ]; then
  LAKE35_EXE="$(command -v "$LAKE35")"
  (cd "$WORK" && PATH="$(dirname "$LAKE35_EXE"):$PATH" "$LAKE35" comparator \
    --config "$CONFIG" \
    --challenge-from-export "$WORK/challenge.ndjson" \
    --solution-from-export "$WORK/solution.ndjson")
  echo "lake comparator exit: $?"
else
  echo "exports complete; the official judge needs Linux+bwrap, so it was NOT run here."
  echo "On a Linux host with the 4.35 toolchain, run:"
  echo "  lake comparator --config $CONFIG \\"
  echo "    --challenge-from-export $WORK/challenge.ndjson \\"
  echo "    --solution-from-export $WORK/solution.ndjson"
  echo "Comparator was NOT run; no passing verification verdict." >&2
  exit 2
fi
