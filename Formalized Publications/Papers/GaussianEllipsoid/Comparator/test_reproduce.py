#!/usr/bin/env python3
"""Test reproduce.sh's error handling with stub executables, never real proof checks.

Run: python3 Comparator/test_reproduce.py
This checks the driver only. It does not claim any Lean proof is valid.
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
    echo "Lean (version 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)"
  else
    echo "Lean (version 4.34.0-rc2, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)"
  fi
  exit 0
fi
if [ "$1" = --run ]; then
  if [ "$DRIVER_TEST_FAILURE" = challenge-export ]; then
    case "$2" in *export34*) exit 18;; esac
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
  echo "Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)"
  exit 0
fi
if [ "$1" = env ]; then
  if [ "$DRIVER_TEST_FAILURE" = bad-leanpath ]; then
    printf '%s:%s\\n' "$DRIVER_TEST_PROJECT/.lake/packages/mathlib/.lake/build/lib/lean" "/foreign/checkout/build/lib/lean"
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
if [ "$DRIVER_TEST_FAILURE" = unsupported-platform ]; then printf 'Darwin\\n'; else printf 'Linux\\n'; fi
"""

SHASUM_STUB = """#!/bin/sh
printf 'stub-hash  %s\\n' "$@"
exit 0
"""


def run_driver(cwd, driver_path, project, work, env):
    return subprocess.run(
        ["sh", str(driver_path), str(project), str(work)],
        cwd=cwd,
        env=env,
        text=True,
        capture_output=True,
        timeout=15,
    )


def main():
    cases = [
        ("none", 0),
        ("bad-34-version", 2),
        ("bad-leanpath", 1),
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
            "lean": LEAN_STUB,
            "lake": LAKE_STUB,
            "uname": UNAME_STUB,
            "shasum": SHASUM_STUB,
            "bwrap": "#!/bin/sh\nexit 0\n",
        }.items():
            path = tools / name
            path.write_text(content)
            path.chmod(0o700)
        project = root / "source project"
        project.mkdir()
        env = dict(os.environ)
        env["PATH"] = str(tools) + os.pathsep + env.get("PATH", "")
        env["DRIVER_TEST_PROJECT"] = str(project)
        for failure, expected in cases:
            env["DRIVER_TEST_FAILURE"] = failure
            # Invoke the actual driver by a relative path from its directory.
            # This also checks that its config still resolves after changing cwd.
            result = run_driver(HERE, "reproduce.sh", project, root / ("work " + failure), env)
            assert result.returncode == expected, (
                failure, result.returncode, expected, result.stdout, result.stderr
            )
            if expected != 0:
                assert "lake comparator exit: 0" not in result.stdout, result.stdout
            print("Driver-only test: %s -> exit %d (expected)" % (failure, expected))
        # Import-guard case: stage a scratch Comparator-like dir whose
        # challenge imports a project module; the driver must refuse (exit 1).
        staged = root / "staged"
        (staged / "Comparator").mkdir(parents=True)
        (staged / "Verification").mkdir(parents=True)
        shutil.copy(HERE / "reproduce.sh", staged / "Comparator" / "reproduce.sh")
        shutil.copy(HERE / "gaussian_ellipsoid_comparator.json",
                    staged / "Comparator" / "gaussian_ellipsoid_comparator.json")
        (staged / "Comparator" / "gaussian_ellipsoid_comparator.lean").write_text(
            "import GaussianEllipsoid.Basic\n")
        (staged / "Verification" / "export34.lean").write_text("-- stub\n")
        env["DRIVER_TEST_FAILURE"] = "none"
        result = run_driver(staged / "Comparator", "reproduce.sh",
                            project, root / "work forbidden-import", env)
        assert result.returncode == 1, (
            "forbidden-import", result.returncode, result.stdout, result.stderr)
        assert "non-external modules" in result.stderr, result.stderr
        print("Driver-only test: forbidden-import -> exit 1 (expected)")
        usage = subprocess.run(["sh", str(DRIVER)], env=env, capture_output=True, timeout=5)
        assert usage.returncode == 2, "Missing arguments must not succeed"
    print("PASS: all driver error-path checks; no proof verification was performed by this test.")


if __name__ == "__main__":
    main()
