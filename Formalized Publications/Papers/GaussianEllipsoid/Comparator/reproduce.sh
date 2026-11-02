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
#   COMPARATOR_BWRAP  `bwrap` binary for the official judge sandbox.
# Each defaults to the PATH lookup of the same name in lowercase
# (`lean`, `lake`, `lake`, `bwrap`), but the 4.34/4.35 version pins are
# asserted before anything runs, so a mixed-up PATH fails closed.
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

for tool in "$LEAN34" "$LAKE34" shasum; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "missing tool: $tool" >&2; exit 2; }
done
[ -f "$CHALLENGE_SRC" ] || { echo "challenge not found: $CHALLENGE_SRC"; exit 2; }
[ -f "$CONFIG" ] || { echo "config not found: $CONFIG"; exit 2; }
[ -f "$SERIALIZER" ] || { echo "serializer not found: $SERIALIZER"; exit 2; }
mkdir -p "$WORK"
WORK="$(cd "$WORK" && pwd)" || exit 2

echo "== 0. toolchain pins"
"$LEAN34" --version | tee "$WORK/toolchain_34.txt" | head -1
grep -q '4\.34\.0-rc2' "$WORK/toolchain_34.txt" || {
  echo "LEAN34 must be Lean 4.34.0-rc2" >&2; exit 2; }
if [ "$(uname -s)" = "Linux" ]; then
  command -v "$LAKE35" >/dev/null 2>&1 || {
    echo "missing tool: $LAKE35" >&2; exit 2; }
  command -v "$COMPARATOR_BWRAP" >/dev/null 2>&1 || {
    echo "missing tool: $COMPARATOR_BWRAP" >&2; exit 2; }
  "$LAKE35" --version | tee "$WORK/toolchain_35.txt" | head -1
  grep -q '4\.35\.0' "$WORK/toolchain_35.txt" || {
    echo "LAKE35 must be Lean 4.35.0" >&2; exit 2; }
fi

echo "== 0b. challenge import guard (external-only)"
grep -h '^import ' "$CHALLENGE_SRC" | grep -v '^import \(Mathlib\|Lean\|Std\|Batteries\)' \
  > "$WORK/forbidden_imports.txt" || true
[ ! -s "$WORK/forbidden_imports.txt" ] || {
  echo "challenge imports non-external modules:" >&2
  cat "$WORK/forbidden_imports.txt" >&2; exit 1; }

# Stage-only search path from the 4.34 workspace, restricted to a curated
# externals whitelist: the scratch dir plus third-party dependency outputs.
# Anything else on the path (project build outputs, foreign checkouts)
# fails closed.
FULL_LP="$(cd "$PROJ" && "$LAKE34" env printenv LEAN_PATH)" || exit 2
MATHLIB_LP=""
REJECTED=""
OLD_IFS="$IFS"; IFS=":"
for entry in $FULL_LP; do
  case "$entry" in
    "$PROJ/.lake/packages/"*)
      MATHLIB_LP="${MATHLIB_LP:+$MATHLIB_LP:}$entry" ;;
    "$PROJ/.lake/build/lib/lean")
      # The solution's own build outputs: expected in the workspace path
      # but never on the challenge (externals-only) search path.
      : ;;
    "")
      ;;
    *)
      REJECTED="${REJECTED:+$REJECTED, }$entry" ;;
  esac
done
IFS="$OLD_IFS"
[ -z "$REJECTED" ] || {
  echo "non-external LEAN_PATH entries rejected: $REJECTED" >&2; exit 1; }
[ -n "$MATHLIB_LP" ] || { echo "empty externals LEAN_PATH" >&2; exit 1; }

echo "== 1. compile challenge (externals-only search path)"
cp "$CHALLENGE_SRC" "$WORK/gaussian_ellipsoid_comparator.lean"
LEAN_PATH="$WORK:$MATHLIB_LP" "$LEAN34" -o "$WORK/gaussian_ellipsoid_comparator.olean" \
  "$WORK/gaussian_ellipsoid_comparator.lean" > "$WORK/challenge_build.log" 2>&1
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
  (cd "$WORK" && "$LAKE35" comparator --config "$CONFIG" \
    --challenge-from-export "$WORK/challenge.ndjson" \
    --solution-from-export "$WORK/solution.ndjson")
  echo "lake comparator exit: $?"
else
  echo "exports complete; the official judge needs Linux+bwrap, so it was NOT run here."
  echo "On a Linux host with the 4.35 toolchain, run:"
  echo "  LAKE35=<4.35 lake> COMPARATOR_BWRAP=<bwrap> \\"
  echo "  $LAKE35 comparator --config $CONFIG \\"
  echo "    --challenge-from-export $WORK/challenge.ndjson \\"
  echo "    --solution-from-export $WORK/solution.ndjson"
  echo "No passing verification verdict without that run." >&2
  exit 2
fi
