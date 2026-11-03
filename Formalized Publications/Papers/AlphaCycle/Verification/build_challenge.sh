#!/bin/sh
# Per-file (fresh-process) build of the AlphaCycle challenge excerpts,
# in dependency order, plus the challenge root module.
#
# Usage: build_challenge.sh <comparator-src-root> <build-out-dir>
#   <comparator-src-root>  Directory holding `alpha_cycle_comparator.lean`
#                          and the `Challenge/` excerpt modules.
#   <build-out-dir>        Scratch directory receiving the `.olean` files
#                          (kept outside git).
#
# Toolchain/search path: same LEAN34 / EXTERNALS_LEAN_PATH convention as
# Verification/build_solution.sh (pinned Lean 4.34.0-rc2 + pinned externals).
#
# Fresh processes are REQUIRED (not an optimization): auto-generated
# auxiliary-lemma numbering depends on per-file elaboration state, and the
# official comparator checks those constants by full body equality.
# Exit 0 with exactly the one authorized `sorry` warning expected.
set -eu
[ "$#" -eq 2 ] || {
  echo "usage: build_challenge.sh <comparator-src-root> <build-out-dir>" >&2
  exit 2; }
SRC="$(cd "$1" && pwd)" || exit 2
BLD="$2"
LEAN34="${LEAN34:-lean}"
[ -n "${EXTERNALS_LEAN_PATH:-}" ] || {
  echo "EXTERNALS_LEAN_PATH is not set (pinned external dependency outputs)" >&2
  exit 2; }
mkdir -p "$BLD"
case "$SRC" in
  "$BLD"/*|"$BLD") echo "build output must not live inside the sources" >&2; exit 2;;
esac
cd "$SRC"
compile_one() {
  mod="$1"
  rel=$(printf '%s' "$mod" | tr '.' '/').lean
  out="$BLD/$(printf '%s' "$mod" | tr '.' '/').olean"
  mkdir -p "$(dirname "$out")"
  # shellcheck disable=SC2086
  LEAN_PATH="$BLD:.:$EXTERNALS_LEAN_PATH" "$LEAN34" -o "$out" "$rel"
}
compile_one Challenge.Section_1_Introduction.Geometry
compile_one Challenge.Section_2_Preliminaries.FiniteLaw
compile_one Challenge.Section_2_Preliminaries.MomentInversion
compile_one Challenge.Section_2_Preliminaries.Polytope
compile_one Challenge.Section_2_Preliminaries.Triangle
compile_one Challenge.Section_2_Preliminaries.Relaxation
compile_one Challenge.Section_2_Preliminaries.DefinitionAudit
compile_one Challenge.Section_2_Preliminaries.PaperCoordinates
compile_one Challenge.Section_2_Preliminaries.GeometryCycle
compile_one Challenge.Section_2_Preliminaries.PaperHypergraph
compile_one Challenge.Section_6_MainTheorem.PaperMain
compile_one alpha_cycle_comparator
echo "CHALLENGE BUILD OK"
