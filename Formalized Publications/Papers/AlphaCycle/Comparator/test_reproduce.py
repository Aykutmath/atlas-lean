#!/usr/bin/env python3
"""Test reproduction-driver guards and failure propagation with stubs.

Run: python3 Comparator/test_reproduce.py
These tests do NOT verify a Lean theorem. Real proof checks use lake comparator.
"""

import os
import shutil
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
DRIVER = HERE / "reproduce.sh"

LEAN_STUB = """#!/bin/sh
if [ "$1" = --version ]; then
  if [ "$DRIVER_TEST_FAILURE" = bad-34-version ]; then
    echo 'Lean (version 4.35.0, Release)'
  else
    echo 'Lean (version 4.34.0-rc2, Release)'
  fi
  if [ "$DRIVER_TEST_FAILURE" = lean-version-exit ]; then exit 17; fi
  exit 0
fi
if [ "$1" = --githash ]; then
  case "$0" in
    *lean35)
      if [ "$DRIVER_TEST_FAILURE" = bad-35-hash ]; then echo deadbeef;
      else echo eb6cafb7290e8bd5f2937522d8d804f58f02bafc; fi ;;
    *)
      if [ "$DRIVER_TEST_FAILURE" = bad-34-hash ]; then echo deadbeef;
      else echo 6a10ac8c22beadecabdbb0919c2b50214762f91d; fi ;;
  esac
  exit 0
fi
if [ "$1" = --run ]; then
  module="$3"
  if [ "$DRIVER_TEST_FAILURE" = challenge-export-fail ]; then
    case "$module" in alpha_cycle_comparator) exit 18;; esac
  fi
  if [ "$DRIVER_TEST_FAILURE" = solution-export-fail ]; then
    case "$module" in AlphaCycle) exit 19;; esac
  fi
  if [ "$DRIVER_TEST_FAILURE" = export-empty ]; then exit 0; fi
  if [ "$DRIVER_TEST_FAILURE" = export-refuse ]; then
    echo "REFUSED: stub export for driver control only" >&2
    exit 0
  fi
  if [ "$DRIVER_TEST_FAILURE" = export-nondet ]; then
    state="$DRIVER_TEST_STATE/$module.count"
    n=0
    if [ -f "$state" ]; then n=$(cat "$state"); fi
    echo $((n + 1)) > "$state"
    extra=",{\\"stub_run\\": $((n + 1))}"
  else
    extra=""
  fi
  shift 3
  if [ "$1" = -- ]; then shift; fi
  DRIVER_TEST_EXTRA="$extra" exec python3 - "$@" <<'PYEOF'
import json, os, sys
roots = sys.argv[1:]
extra = os.environ.get("DRIVER_TEST_EXTRA", "")
ids, order = {}, []
def intern(dotted):
    pre = 0
    for part in dotted.split("."):
        key = (pre, part)
        if key not in ids:
            ids[key] = len(order) + 1
            order.append(key)
        pre = ids[key]
    return pre
for r in roots:
    intern(r)
for i, (pre, part) in enumerate(order, start=1):
    if part.isdigit():
        print(json.dumps({"in": i, "num": {"pre": pre, "i": int(part)}}))
    else:
        print(json.dumps({"in": i, "str": {"pre": pre, "str": part}}))
if extra:
    print(extra)
PYEOF
  exit 0
fi
if [ "$DRIVER_TEST_FAILURE" = compile-fail ]; then exit 17; fi
while [ "$#" -gt 0 ]; do
  if [ "$1" = -o ]; then
    shift
    printf 'stub output for driver control only\\n' > "$1"
    case "$1" in
      *alpha_cycle_comparator.olean)
        printf 'alpha_cycle_comparator.lean:28:0: warning: declaration uses `sorry`\\n' ;;
      *)
        if [ "$DRIVER_TEST_FAILURE" = sorry-count ]; then
          printf 'stub.lean:1:0: warning: declaration uses `sorry`\\n'
        fi ;;
    esac
    exit 0
  fi
  shift
done
exit 0
"""

LAKE_STUB = """#!/bin/sh
if [ "$1" = --version ]; then
  echo 'Lake version 5.0.0-src (Lean version 4.35.0)'
  if [ "$DRIVER_TEST_FAILURE" = lake-version-exit ]; then exit 18; fi
  exit 0
fi
if [ "$1" = comparator ]; then
  if [ "$DRIVER_TEST_FAILURE" = comparison ]; then exit 23; fi
  case "$2" in --config) test -f "$3" || exit 24;; esac
  printf 'stub comparator for driver control only\\n'
  exit 0
fi
exit 25
"""

UNAME_STUB = """#!/bin/sh
if [ "$DRIVER_TEST_FAILURE" = unsupported-platform ]; then printf 'Darwin\\n';
else printf 'Linux\\n'; fi
"""

SHASUM_STUB = """#!/bin/sh
printf 'stub-hash  %s\\n' "$@"
exit 0
"""


def run_driver(cwd, driver, project, work, env):
    return subprocess.run(
        ["sh", str(driver), str(project), str(work)],
        cwd=cwd, env=env, text=True, capture_output=True, timeout=120,
    )


def assert_exit(label, result, expected):
    assert result.returncode == expected, (
        label, result.returncode, expected, result.stdout, result.stderr,
    )
    if expected:
        assert "lake comparator exit: 0" not in result.stdout, result.stdout
    print("Driver-only test: %s -> exit %d (expected)" % (label, expected))


def main():
    cases = [
        ("none", 0),
        ("bad-34-version", 2),
        ("bad-34-hash", 2),
        ("lean-version-exit", 17),
        ("bad-35-hash", 2),
        ("lake-version-exit", 18),
        ("compile-fail", 17),
        ("sorry-count", 1),
        ("challenge-export-fail", 1),
        ("solution-export-fail", 1),
        ("export-empty", 1),
        ("export-refuse", 1),
        ("export-nondet", 1),
        ("comparison", 23),
        ("unsupported-platform", 2),
    ]
    with tempfile.TemporaryDirectory(prefix="alpha-driver-test-") as temp:
        root = Path(temp)
        tools = root / "stub-bin"
        tools.mkdir()
        for name, content in {
            "lean34": LEAN_STUB,
            "lean35": LEAN_STUB,
            "lake35": LAKE_STUB,
            "uname": UNAME_STUB,
            "shasum": SHASUM_STUB,
            "sha256sum": SHASUM_STUB,
            "bwrap": "#!/bin/sh\nexit 0\n",
        }.items():
            path = tools / name
            path.write_text(content)
            path.chmod(0o700)
        project = root / "source project"
        shutil.copytree(HERE / "..", project)
        ext1 = root / "ext1"
        ext2 = root / "ext2"
        ext1.mkdir()
        ext2.mkdir()
        (ext1 / "Mathlib.olean").write_text("stub\n")
        state = root / "export-state"
        state.mkdir()
        env = dict(os.environ)
        env.update({
            "PATH": str(tools) + os.pathsep + env.get("PATH", ""),
            "LEAN34": str(tools / "lean34"),
            "LEAN35": str(tools / "lean35"),
            "LAKE35": str(tools / "lake35"),
            "COMPARATOR_BWRAP": str(tools / "bwrap"),
            "EXTERNALS_LEAN_PATH": str(ext1) + os.pathsep + str(ext2),
            "DRIVER_TEST_STATE": str(state),
        })
        for failure, expected in cases:
            env["DRIVER_TEST_FAILURE"] = failure
            for old in state.glob("*.count"):
                old.unlink()
            result = run_driver(root, DRIVER, project, root / ("work " + failure), env)
            assert_exit(failure, result, expected)
        env["DRIVER_TEST_FAILURE"] = "none"

        missing = dict(env, COMPARATOR_BWRAP=str(root / "missing-bwrap"))
        assert_exit("missing-bwrap",
                    run_driver(root, DRIVER, project,
                               root / "work missing bwrap", missing), 2)

        for label, externals in [
            ("externals-relative", "relative/dir:" + str(ext1)),
            ("externals-missing", str(root / "no-such-dir") + ":" + str(ext1)),
            ("externals-no-mathlib", str(ext2)),
            ("externals-inside-package", str(project)),
        ]:
            bad = dict(env, EXTERNALS_LEAN_PATH=externals)
            assert_exit(label,
                        run_driver(root, DRIVER, project,
                                   root / ("work " + label), bad), 1)

        staged = root / "staged tamper"
        shutil.copytree(project, staged)
        (staged / "Formalization" / "Section_6_MainTheorem" /
         "PaperMain.lean").write_text(
            "theorem paper_sharp_classification : True := by sorry\n")
        assert_exit("solution-sorry",
                    run_driver(root, DRIVER, staged,
                               root / "work solution sorry", env), 1)

        for label, import_line in [
            ("forbidden-import", "import AlphaCycle.Section_1_Introduction.Geometry"),
            ("indented-forbidden-import", "  import AlphaCycle.Basic"),
            ("fake-mathlib-prefix", "import MathlibShadow"),
        ]:
            tampered = root / label
            shutil.copytree(project, tampered)
            source = (tampered / "Comparator" /
                      "alpha_cycle_comparator.lean").read_text()
            source = source.replace(
                "import Challenge.Section_6_MainTheorem.PaperMain",
                import_line, 1)
            (tampered / "Comparator" /
             "alpha_cycle_comparator.lean").write_text(source)
            result = run_driver(root, tampered / "Comparator" / "reproduce.sh",
                                  tampered, root / ("work " + label), env)
            assert_exit(label, result, 1)
            assert "non-external modules" in result.stderr, result.stderr

        usage = subprocess.run(["sh", str(DRIVER)], env=env,
                               capture_output=True, text=True, timeout=30)
        assert_exit("missing-arguments", usage, 2)
    print("PASS: driver guards and error paths only; no theorem was checked by these stub tests.")


if __name__ == "__main__":
    main()
