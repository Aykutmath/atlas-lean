#!/bin/sh
# Negative controls for the Alpha-Cycle independent comparator.
#
# Usage: negative_controls.sh <package-root> <work-dir>
#
# Runs on Linux only (exit 2 elsewhere): each control rebuilds a tampered
# variant with the pinned 4.34 toolchain, exports it with the 4.34
# serializer, and requires the official 4.35 `lake comparator` to REJECT it
# (nonzero exit). A control that the judge accepts is a failure of this
# script (exit 1): the comparator would be vacuous.
#
# Environment: same LEAN34 / EXTERNALS_LEAN_PATH / LAKE35 / LEAN35 /
# COMPARATOR_BWRAP convention as Comparator/reproduce.sh. LEAN34 must be a
# Lean 4.34.0-rc2 binary on this Linux host (e.g. via elan); the pinned
# external outputs must already be assembled (see the package Readme).
#
# Controls (solution held fixed unless stated):
#   N1 incorrect-polytope  challenge `polytope` replaced by the empty set.
#   N2 wrong-cycle         challenge `cycleDistinguishedRelaxation` built from
#                          the all-cycles relaxation instead of the
#                          distinguished cycle (drops the cycle object).
#   N3 identity-relaxation challenge `cycleAllRelaxation` replaced by empty.
#   N4 sorry-solution      solution main theorem proved by `sorry`.
#   N5 threshold-tamper    challenge classification threshold `= 1` weakened
#                          to `= 2` (statement sensitivity).
#
# N1-N3/N5 tamper the challenge side while holding the solution fixed. That
# exercises exactly the same constant-equality check the judge applies to
# solution deviations (`challengeConst != solutionConst` is symmetric), and
# keeps every variant compiling cleanly: the challenge's only proof
# obligation is the sorry'd main theorem, so same-type definition tampers
# cannot break any proof. N4 is solution-side. Every control asserts its
# tamper actually changed the export (non-vacuous) and that the judge
# rejects it.
set -eu
[ "$#" -eq 2 ] || {
  echo "usage: negative_controls.sh <package-root> <work-dir>" >&2; exit 2; }
PKG="$(cd "$1" && pwd)" || exit 2
WORK="$2"
SCRIPT_DIR="$(CDPATH= cd "$(dirname "$0")" && pwd)" || exit 2
CONFIG="$SCRIPT_DIR/alpha_cycle_comparator.json"
SERIALIZER="$SCRIPT_DIR/../Verification/export34.lean"
BUILD_SOLUTION="$SCRIPT_DIR/../Verification/build_solution.sh"
BUILD_CHALLENGE="$SCRIPT_DIR/../Verification/build_challenge.sh"
CHECK_EXPORTS="$SCRIPT_DIR/../Verification/check_exports.py"
GUARDS="$SCRIPT_DIR/guard_inputs.py"

[ "$(uname -s)" = "Linux" ] || {
  echo "negative controls need Linux+bwrap (same as the official judge)" >&2
  exit 2; }
LEAN34="${LEAN34:-lean}"
LAKE35="${LAKE35:-lake}"
COMPARATOR_BWRAP="${COMPARATOR_BWRAP:-bwrap}"
export COMPARATOR_BWRAP
for tool in "$LEAN34" python3; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "missing tool: $tool" >&2; exit 2; }
done
command -v "$LAKE35" >/dev/null 2>&1 || {
  echo "missing tool: $LAKE35" >&2; exit 2; }
command -v "$COMPARATOR_BWRAP" >/dev/null 2>&1 || {
  echo "missing tool: $COMPARATOR_BWRAP" >&2; exit 2; }
[ -n "${EXTERNALS_LEAN_PATH:-}" ] || {
  echo "EXTERNALS_LEAN_PATH is not set" >&2; exit 2; }
"$LEAN34" --version > /dev/null
[ "$("$LEAN34" --githash)" = 6a10ac8c22beadecabdbb0919c2b50214762f91d ] || {
  echo "LEAN34 commit does not match the verified toolchain" >&2; exit 2; }
LAKE35_EXE="$(command -v "$LAKE35")"
export PATH="$(dirname "$LAKE35_EXE"):$PATH"
mkdir -p "$WORK"
WORK="$(cd "$WORK" && pwd)" || exit 2

ROOTS="Quot Quot.mk Quot.lift Quot.ind AlphaCycle.PaperHypergraph.paper_sharp_classification propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"

MATHLIB_LP="$EXTERNALS_LEAN_PATH"
export EXTERNALS_LEAN_PATH="$MATHLIB_LP"

run_export() {
  # run_export <module> <build-dir> <out-ndjson> <log>
  mod="$1"; bld="$2"; out="$3"; log="$4"
  LEAN_PATH="$bld:$MATHLIB_LP" "$LEAN34" --run "$SERIALIZER" \
    "$mod" -- $ROOTS > "$out" 2>"$log" || true
  test -s "$out" || { echo "export is empty: $out" >&2; return 1; }
  if grep -q "REFUSED\|uncaught exception" "$log"; then
    echo "export refused: $out" >&2; return 1; fi
  python3 "$CHECK_EXPORTS" "$out" $ROOTS || return 1
}

run_judge() {
  # run_judge <challenge-ndjson> <solution-ndjson> <log>; returns judge exit.
  (cd "$WORK" && "$LAKE35" comparator --config "$CONFIG" \
    --challenge-from-export "$1" --solution-from-export "$2" \
    > "$3" 2>&1)
}

echo "== positive control first (good pair must pass)"
LEAN34="$LEAN34" sh "$BUILD_SOLUTION" "$PKG/Formalization" \
  "$WORK/good_solution" > "$WORK/good_solution.log" 2>&1
LEAN34="$LEAN34" sh "$BUILD_CHALLENGE" "$PKG/Comparator" \
  "$WORK/good_challenge" > "$WORK/good_challenge.log" 2>&1
run_export AlphaCycle "$WORK/good_solution" \
  "$WORK/good_solution.ndjson" "$WORK/good_solution_export.log"
run_export alpha_cycle_comparator "$WORK/good_challenge" \
  "$WORK/good_challenge.ndjson" "$WORK/good_challenge_export.log"
if run_judge "$WORK/good_challenge.ndjson" "$WORK/good_solution.ndjson" \
    "$WORK/positive.log"; then
  echo "positive control: PASS (judge exit 0)"
else
  echo "positive control FAILED (judge rejected the good pair)" >&2
  cat "$WORK/positive.log" >&2; exit 1; fi

PASS=0; FAIL=0
expect_reject() {
  # expect_reject <name> <challenge-ndjson> <solution-ndjson>
  name="$1"
  if run_judge "$2" "$3" "$WORK/judge_$name.log"; then
    echo "$name: FAIL (judge accepted a tampered variant)" >&2
    FAIL=$((FAIL + 1))
  else
    echo "$name: PASS (judge rejected as required)"
    PASS=$((PASS + 1))
  fi
}
hash_differs() {
  # hash_differs <name> <good-ndjson> <variant-ndjson>
  if cmp -s "$2" "$3"; then
    echo "$1: FAIL (variant export identical to good export)" >&2
    FAIL=$((FAIL + 1)); return 1
  fi
  return 0
}
rebuild_challenge_variant() {
  # rebuild_challenge_variant <variant-dir> (Comparator tree already tampered)
  LEAN34="$LEAN34" sh "$BUILD_CHALLENGE" "$1" "$WORK/challenge_$2" \
    > "$WORK/challenge_$2.log" 2>&1
}

echo "== N1 incorrect-polytope (challenge)"
rm -rf "$WORK/n1" && cp -r "$PKG/Comparator" "$WORK/n1"
python3 - "$WORK/n1/Challenge/Section_2_Preliminaries/PaperCoordinates.lean" <<'EOF'
import sys
p = sys.argv[1]
src = open(p).read()
old = "def polytope : Set H.Vector := convexHull \u211d H.multilinearSet"
assert src.count(old) == 1, "N1 anchor not unique"
open(p, "w").write(src.replace(old, "def polytope : Set H.Vector := \u2205"))
print("N1 tamper applied")
EOF
rebuild_challenge_variant "$WORK/n1" n1
if [ "$(grep -c 'declaration uses .sorry.' "$WORK/challenge_n1.log" || true)" != "1" ]; then echo "n1: FAIL (sorry count changed)"; FAIL=$((FAIL + 1)); fi
run_export alpha_cycle_comparator "$WORK/challenge_n1" \
  "$WORK/n1.ndjson" "$WORK/n1_export.log"
if hash_differs N1 "$WORK/good_challenge.ndjson" "$WORK/n1.ndjson"; then
  expect_reject N1 "$WORK/n1.ndjson" "$WORK/good_solution.ndjson"
fi

echo "== N2 wrong-cycle-relaxation (challenge)"
rm -rf "$WORK/n2" && cp -r "$PKG/Comparator" "$WORK/n2"
python3 - "$WORK/n2/Challenge/Section_6_MainTheorem/PaperMain.lean" <<'EOF'
import sys
p = sys.argv[1]
src = open(p).read()
old = "AlphaCycle.distinguishedRelaxation e (Geometry.distinguishedCycle e hc)"
assert src.count(old) == 1, "N2 anchor not unique"
open(p, "w").write(src.replace(old, "AlphaCycle.allCycleRelaxation e"))
print("N2 tamper applied")
EOF
rebuild_challenge_variant "$WORK/n2" n2
if [ "$(grep -c 'declaration uses .sorry.' "$WORK/challenge_n2.log" || true)" != "1" ]; then echo "n2: FAIL (sorry count changed)"; FAIL=$((FAIL + 1)); fi
run_export alpha_cycle_comparator "$WORK/challenge_n2" \
  "$WORK/n2.ndjson" "$WORK/n2_export.log"
if hash_differs N2 "$WORK/good_challenge.ndjson" "$WORK/n2.ndjson"; then
  expect_reject N2 "$WORK/n2.ndjson" "$WORK/good_solution.ndjson"
fi

echo "== N3 identity-relaxation (challenge)"
rm -rf "$WORK/n3" && cp -r "$PKG/Comparator" "$WORK/n3"
python3 - "$WORK/n3/Challenge/Section_6_MainTheorem/PaperMain.lean" <<'EOF'
import sys
p = sys.argv[1]
src = open(p).read()
old = "  cycleCoordinates e hc hv \u207b\u00b9' AlphaCycle.allCycleRelaxation e"
assert src.count(old) == 1, "N3 anchor not unique"
open(p, "w").write(src.replace(old, "  \u2205"))
print("N3 tamper applied")
EOF
rebuild_challenge_variant "$WORK/n3" n3
if [ "$(grep -c 'declaration uses .sorry.' "$WORK/challenge_n3.log" || true)" != "1" ]; then echo "n3: FAIL (sorry count changed)"; FAIL=$((FAIL + 1)); fi
run_export alpha_cycle_comparator "$WORK/challenge_n3" \
  "$WORK/n3.ndjson" "$WORK/n3_export.log"
if hash_differs N3 "$WORK/good_challenge.ndjson" "$WORK/n3.ndjson"; then
  expect_reject N3 "$WORK/n3.ndjson" "$WORK/good_solution.ndjson"
fi

echo "== N4 sorry-solution (solution)"
rm -rf "$WORK/n4" && cp -r "$PKG/Formalization" "$WORK/n4"
python3 - "$WORK/n4/Section_6_MainTheorem/PaperMain.lean" <<'EOF'
import sys
p = sys.argv[1]
src = open(p).read()
start = src.index("theorem paper_sharp_classification")
byidx = src.index(":= by", start) + len(":= by")
head, tail = src[:byidx], src[byidx:]
# the proof runs to end of file except the trailing namespace closer
closer = "\nend AlphaCycle.PaperHypergraph\n"
assert tail.rstrip().endswith(closer.strip()), "N4 unexpected file tail"
open(p, "w").write(head + "\n  sorry\n" + closer)
print("N4 tamper applied")
EOF
rm -rf "$WORK/solution_n4" && mkdir -p "$WORK/solution_n4"
cp -r "$WORK/good_solution/." "$WORK/solution_n4/"
(cd "$WORK/n4" && LEAN_PATH="$WORK/solution_n4:.:$MATHLIB_LP" "$LEAN34" \
  -o "$WORK/solution_n4/Section_6_MainTheorem/PaperMain.olean" \
  Section_6_MainTheorem/PaperMain.lean > "$WORK/solution_n4_papermain.log" 2>&1)
(cd "$WORK/n4" && LEAN_PATH="$WORK/solution_n4:.:$MATHLIB_LP" "$LEAN34" \
  -o "$WORK/solution_n4/AlphaCycle.olean" AlphaCycle.lean \
  > "$WORK/solution_n4_root.log" 2>&1)
grep -q 'declaration uses .sorry.' "$WORK/solution_n4_papermain.log" || {
  echo "N4: FAIL (sorry not present in tampered solution)" >&2
  FAIL=$((FAIL + 1)); }
run_export AlphaCycle "$WORK/solution_n4" \
  "$WORK/n4.ndjson" "$WORK/n4_export.log"
if hash_differs N4 "$WORK/good_solution.ndjson" "$WORK/n4.ndjson"; then
  expect_reject N4 "$WORK/good_challenge.ndjson" "$WORK/n4.ndjson"
fi

echo "== N5 threshold-tamper (challenge statement)"
rm -rf "$WORK/n5" && cp -r "$PKG/Comparator" "$WORK/n5"
python3 - "$WORK/n5/Challenge/Section_6_MainTheorem/PaperMain.lean" <<'EOF'
import sys
p = sys.argv[1]
lines = open(p).read().split("\n")
start = next(i for i, l in enumerate(lines)
             if l.startswith("theorem paper_sharp_classification"))
end = next(i for i in range(start, len(lines)) if "sorry" in lines[i])
block = "\n".join(lines[start:end + 1])
assert block.count("= 1") == 6, block.count("= 1")
lines[start:end + 1] = block.replace("= 1", "= 2").split("\n")
open(p, "w").write("\n".join(lines))
print("N5 tamper applied")
EOF
rebuild_challenge_variant "$WORK/n5" n5
if [ "$(grep -c 'declaration uses .sorry.' "$WORK/challenge_n5.log" || true)" != "1" ]; then echo "n5: FAIL (sorry count changed)"; FAIL=$((FAIL + 1)); fi
run_export alpha_cycle_comparator "$WORK/challenge_n5" \
  "$WORK/n5.ndjson" "$WORK/n5_export.log"
if hash_differs N5 "$WORK/good_challenge.ndjson" "$WORK/n5.ndjson"; then
  expect_reject N5 "$WORK/n5.ndjson" "$WORK/good_solution.ndjson"
fi

echo "negative controls: $PASS passed, $FAIL failed"
[ "$FAIL" = "0" ] && [ "$PASS" = "5" ]
