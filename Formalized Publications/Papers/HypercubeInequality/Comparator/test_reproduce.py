#!/usr/bin/env python3
"""Test reproduce.sh's error handling with stub executables, never real proof checks.

Run: python3 Comparator/test_reproduce.py
This checks the driver only. It does not claim any Lean proof is valid.
"""

import os
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
DRIVER = HERE / "reproduce.sh"

LEAN_STUB = """#!/bin/sh
if [ "$DRIVER_TEST_FAILURE" = compile ]; then exit 17; fi
while [ "$#" -gt 0 ]; do
  if [ "$1" = -o ]; then
    shift
    printf 'stub output for driver control only\n' > "$1"
    exit 0
  fi
  shift
done
exit 0
"""

LAKE_STUB = """#!/bin/sh
if [ "$1" = env ]; then
  printf '%s:%s\n' "$DRIVER_TEST_PROJECT/.lake/packages/mathlib/.lake/build/lib/lean" "$DRIVER_TEST_PROJECT/.lake/build/lib/lean"
  exit 0
fi
if [ "$1" = comparator ]; then
  if [ "$DRIVER_TEST_FAILURE" = comparison ]; then exit 23; fi
  case "$2" in --config) test -f "$3" || exit 24;; esac
  printf 'stub comparator for driver control only\n'
  exit 0
fi
exit 25
"""

EXPORT_STUB = """#!/bin/sh
case "$1" in
  hypercube_inequality_comparator)
    if [ "$DRIVER_TEST_FAILURE" = challenge-export ]; then exit 18; fi;;
  HypercubeInequality)
    if [ "$DRIVER_TEST_FAILURE" = solution-export ]; then exit 19; fi;;
esac
printf 'stub export for driver control only\n'
"""

UNAME_STUB = """#!/bin/sh
if [ "$DRIVER_TEST_FAILURE" = unsupported-platform ]; then printf 'Darwin\n'; else printf 'Linux\n'; fi
"""


def main():
    cases = [
        ("none", 0),
        ("compile", 17),
        ("challenge-export", 18),
        ("solution-export", 19),
        ("comparison", 23),
        ("unsupported-platform", 2),
    ]
    with tempfile.TemporaryDirectory(prefix="hypercube-driver-test-") as temp:
        root = Path(temp)
        tools = root / "stub-bin"
        tools.mkdir()
        for name, content in {
            "lean": LEAN_STUB,
            "lake": LAKE_STUB,
            "leanexport": EXPORT_STUB,
            "uname": UNAME_STUB,
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
            result = subprocess.run(
                ["sh", "reproduce.sh", str(project), str(root / ("work " + failure))],
                cwd=HERE,
                env=env,
                text=True,
                capture_output=True,
                timeout=15,
            )
            assert result.returncode == expected, (
                failure, result.returncode, expected, result.stdout, result.stderr
            )
            if expected != 0:
                assert "lake comparator exit: 0" not in result.stdout, result.stdout
            print("Driver-only test: %s -> exit %d (expected)" % (failure, expected))
        usage = subprocess.run(["sh", str(DRIVER)], env=env, capture_output=True, timeout=5)
        assert usage.returncode == 2, "Missing arguments must not succeed"
    print("PASS: all driver error-path checks; no proof verification was performed by this test.")


if __name__ == "__main__":
    main()
