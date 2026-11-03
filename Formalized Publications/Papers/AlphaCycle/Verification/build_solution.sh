#!/bin/sh
# Direct-Lean topological rebuild of the AlphaCycle solution from sources.
#
# Usage: build_solution.sh <formalization-src-root> <build-out-dir>
#   <formalization-src-root>  Directory holding `AlphaCycle.lean` and the
#                             `Section_*` folders (package `Formalization/`).
#   <build-out-dir>            Scratch directory receiving the `.olean` files
#                             in module-mirror layout (kept outside git).
#
# Toolchain: LEAN34 must be the pinned Lean 4.34.0-rc2 binary
# (commit 6a10ac8c22beadecabdbb0919c2b50214762f91d). Search path:
# EXTERNALS_LEAN_PATH (colon-separated pinned external dependency outputs:
# Mathlib at 85e3a25e006c35636f0e53b0e9296caca2685bc0 plus its eight pinned
# companion packages; see the package Readme for the assembly recipe).
#
# Each module is elaborated in its own `lean` process, in dependency order
# (fresh elaboration state per file, exactly like the verified build).
# Exit 0 with no `sorry`/`admit` warnings expected; any error fails closed.
set -eu
[ "$#" -eq 2 ] || {
  echo "usage: build_solution.sh <formalization-src-root> <build-out-dir>" >&2
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
compile_one Section_1_Introduction.Geometry
compile_one Section_3_Obstruction.FourVariable
compile_one Section_2_Preliminaries.Triangle
compile_one Section_2_Preliminaries.AllCycles
compile_one Section_2_Preliminaries.FiniteLaw
compile_one Section_2_Preliminaries.Basic
compile_one Section_2_Preliminaries.Core
compile_one Section_2_Preliminaries.MomentInversion
compile_one Section_2_Preliminaries.Polytope
compile_one Section_2_Preliminaries.Relaxation
compile_one Section_2_Preliminaries.CyclePermutation
compile_one Section_2_Preliminaries.DefinitionAudit
compile_one Section_2_Preliminaries.GeometryCycle
compile_one Section_2_Preliminaries.Gluing
compile_one Section_2_Preliminaries.LocalVector
compile_one Section_2_Preliminaries.MomentConverse
compile_one Section_2_Preliminaries.PaperCoordinates
compile_one Section_2_Preliminaries.PaperHypergraph
compile_one Section_2_Preliminaries.PaperCycleCorrespondence
compile_one Section_2_Preliminaries.SetGluing
compile_one Section_2_Preliminaries.PaperGeometry
compile_one Section_2_Preliminaries.PaperTranscription
compile_one Section_2_Preliminaries.PaperInversionIdentities
compile_one Section_2_Preliminaries.PaperTriangles
compile_one Section_2_Preliminaries.Reindex
compile_one Section_4_Negative.Negative
compile_one Section_4_Negative.NegativeVertex
compile_one Section_4_Negative.NegativeSwitched
compile_one Section_4_Negative.NegativeTheorem
compile_one Section_5_Positive.PositiveSlice
compile_one Section_5_Positive.Positive
compile_one Section_5_Positive.Singleton
compile_one Section_5_Positive.SliceBridge
compile_one Section_5_Positive.PositiveTheorem
compile_one Section_6_MainTheorem.Main
compile_one Section_3_Obstruction.Examples
compile_one Section_3_Obstruction.PaperExampleDetails
compile_one Section_3_Obstruction.PaperObstruction
compile_one Section_4_Negative.PaperEvents
compile_one Section_5_Positive.PaperKernels
compile_one Section_5_Positive.PaperSlices
compile_one Section_5_Positive.PrivateBlocks
compile_one Section_6_MainTheorem.PaperConvexCombination
compile_one Section_6_MainTheorem.PaperMain
compile_one AlphaCycle
echo "SOLUTION BUILD OK"
