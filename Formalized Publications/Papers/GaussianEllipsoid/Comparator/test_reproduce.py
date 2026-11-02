#!/usr/bin/env python3
"""Test reproduction-driver guards and failure propagation with stubs.

Run: python3 Comparator/test_reproduce.py
These tests do NOT verify a Lean theorem. Real proof checks use lake comparator.
"""

import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

from guard_inputs import DEPENDENCY_PINS

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
  if [ "$DRIVER_TEST_FAILURE" = challenge-export ]; then
    case "$3" in gaussian_ellipsoid_comparator) exit 18;; esac
  fi
  if [ "$DRIVER_TEST_FAILURE" = solution-export ]; then
    case "$3" in GaussianEllipsoid) exit 19;; esac
  fi
  printf '{"meta":"stub export for driver control only"}\\n'
  exit 0
fi
if [ "$DRIVER_TEST_FAILURE" = compile ]; then exit 17; fi
while [ "$#" -gt 0 ]; do
  if [ "$1" = -o ]; then
    shift
    printf 'stub output for driver control only\\n' > "$1"
    if [ "$DRIVER_TEST_FAILURE" != sorry-count ]; then
      printf 'gaussian_ellipsoid_comparator.lean:177:8: warning: declaration uses `sorry`\\n'
    fi
    exit 0
  fi
  shift
done
exit 0
"""

LAKE_STUB = """#!/bin/sh
if [ "$1" = --version ]; then
  case "$0" in
    *lake34)
      if [ "$DRIVER_TEST_FAILURE" = bad-lake34-version ]; then
        echo 'Lake version 5.0.0-src (Lean version 4.35.0)'
      else
        echo 'Lake version 5.0.0-src (Lean version 4.34.0-rc2)'
      fi ;;
    *)
      echo 'Lake version 5.0.0-src (Lean version 4.35.0)'
      if [ "$DRIVER_TEST_FAILURE" = lake-version-exit ]; then exit 18; fi ;;
  esac
  exit 0
fi
if [ "$1" = env ]; then
  if [ "$DRIVER_TEST_FAILURE" = bad-leanpath ]; then
    printf '%s:%s\\n' "$DRIVER_TEST_PROJECT/.lake/packages/mathlib/.lake/build/lib/lean" '/foreign/checkout/build/lib/lean'
  elif [ "$DRIVER_TEST_FAILURE" = hidden-project-package ]; then
    printf '%s:%s\\n' "$DRIVER_TEST_PROJECT/.lake/packages/mathlib/.lake/build/lib/lean" "$DRIVER_TEST_PROJECT/.lake/packages/HiddenSolution/.lake/build/lib/lean"
  else
    printf '%s:%s\\n' "$DRIVER_TEST_PROJECT/.lake/packages/mathlib/.lake/build/lib/lean" "$DRIVER_TEST_PROJECT/.lake/build/lib/lean"
  fi
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


def run_driver(cwd, driver_path, project, work, env):
    return subprocess.run(
        ["sh", str(driver_path), str(project), str(work)],
        cwd=cwd, env=env, text=True, capture_output=True, timeout=20,
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
        ("bad-lake34-version", 2),
        ("bad-34-hash", 2),
        ("bad-35-hash", 2),
        ("lean-version-exit", 17),
        ("lake-version-exit", 18),
        ("bad-leanpath", 1),
        ("hidden-project-package", 1),
        ("compile", 17),
        ("sorry-count", 1),
        ("challenge-export", 18),
        ("solution-export", 19),
        ("comparison", 23),
        ("unsupported-platform", 2),
    ]
    with tempfile.TemporaryDirectory(prefix="gaussian-driver-test-") as temp:
        root = Path(temp)
        tools = root / "stub-bin"
        tools.mkdir()
        for name, content in {
            "lean34": LEAN_STUB,
            "lean35": LEAN_STUB,
            "lake34": LAKE_STUB,
            "lake35": LAKE_STUB,
            "uname": UNAME_STUB,
            "shasum": SHASUM_STUB,
            "bwrap": "#!/bin/sh\nexit 0\n",
        }.items():
            path = tools / name
            path.write_text(content)
            path.chmod(0o700)
        project = root / "source project"
        project.mkdir()
        manifest = {
            "packagesDir": ".lake/packages",
            "packages": [{"name": name, "rev": rev} for name, rev in DEPENDENCY_PINS.items()],
        }
        (project / "lake-manifest.json").write_text(json.dumps(manifest))
        for name in DEPENDENCY_PINS:
            (project / ".lake/packages" / name / ".lake/build/lib/lean").mkdir(parents=True)
        (project / ".lake/build/lib/lean").mkdir(parents=True)
        env = dict(os.environ)
        env.update({
            "PATH": str(tools) + os.pathsep + env.get("PATH", ""),
            "DRIVER_TEST_PROJECT": str(project),
            "LEAN34": str(tools / "lean34"),
            "LAKE34": str(tools / "lake34"),
            "LEAN35": str(tools / "lean35"),
            "LAKE35": str(tools / "lake35"),
            "COMPARATOR_BWRAP": str(tools / "bwrap"),
        })
        for failure, expected in cases:
            env["DRIVER_TEST_FAILURE"] = failure
            result = run_driver(HERE, "reproduce.sh", project, root / ("work " + failure), env)
            assert_exit(failure, result, expected)

        env["DRIVER_TEST_FAILURE"] = "none"
        missing = dict(env, COMPARATOR_BWRAP=str(root / "missing-bwrap"))
        assert_exit("missing-bwrap", run_driver(HERE, "reproduce.sh", project, root / "work missing bwrap", missing), 2)

        for label, import_line in [
            ("forbidden-import", "import GaussianEllipsoid.Basic"),
            ("public-forbidden-import", "public import GaussianEllipsoid.Basic"),
            ("indented-forbidden-import", "  import GaussianEllipsoid.Basic"),
            ("fake-mathlib-prefix", "import MathlibShadow"),
        ]:
            staged = root / label
            (staged / "Comparator").mkdir(parents=True)
            (staged / "Verification").mkdir()
            for filename in ["reproduce.sh", "guard_inputs.py", "gaussian_ellipsoid_comparator.json"]:
                shutil.copy(HERE / filename, staged / "Comparator" / filename)
            source = (HERE / "gaussian_ellipsoid_comparator.lean").read_text()
            source = source.replace("import Mathlib", import_line, 1)
            (staged / "Comparator/gaussian_ellipsoid_comparator.lean").write_text(source)
            (staged / "Verification/export34.lean").write_text("-- stub\n")
            result = run_driver(staged / "Comparator", "reproduce.sh", project, root / ("work " + label), env)
            assert_exit(label, result, 1)
            assert "non-external modules" in result.stderr, result.stderr

        bad_manifest = json.loads(json.dumps(manifest))
        bad_manifest["packages"][0]["rev"] = "0" * 40
        (project / "lake-manifest.json").write_text(json.dumps(bad_manifest))
        assert_exit("wrong-mathlib-pin", run_driver(HERE, "reproduce.sh", project, root / "work wrong pin", env), 1)
        (project / "lake-manifest.json").write_text(json.dumps(manifest))

        usage = subprocess.run(["sh", str(DRIVER)], env=env, capture_output=True, text=True, timeout=5)
        assert_exit("missing-arguments", usage, 2)
    print("PASS: driver guards and error paths only; no theorem was checked by these stub tests.")


if __name__ == "__main__":
    main()
