#!/usr/bin/env python3
"""Fail-closed input guards for the independent Gaussian comparator.

These are source/path hygiene checks, not a Lean proof checker. The official
comparator and its kernel still decide the proof verdict.
"""

import json
import re
import sys
from pathlib import Path

EXPECTED_CONFIG = {
    "challenge_module": "gaussian_ellipsoid_comparator",
    "solution_module": "GaussianEllipsoid",
    "theorem_names": ["GaussianEllipsoid.strict_threshold_unconditional"],
    "definition_names": [],
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
}

DEPENDENCY_PINS = {
    "mathlib": "85e3a25e006c35636f0e53b0e9296caca2685bc0",
    "plausible": "d9598f07b1bc701f1e3aae163d2681c1fd978793",
    "LeanSearchClient": "ba67e212be1197b84c1f1f6299488a10a3002713",
    "importGraph": "d8823026ac7ef130c253089d95685f9877b95323",
    "proofwidgets": "a8acbfd87375ff4abe14ce09db5b7664d383bc7f",
    "aesop": "18889deb9e83ea7420ef51c160d6f88552e744e3",
    "Qq": "507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3",
    "batteries": "d54dddc581e08be364c278052863524bff7a99a9",
    "Cli": "ab3a82db9fea14cf0fd7f5a2de650f4b534640af",
}


def fail(message):
    raise SystemExit("Comparator input guard: " + message)


def code_only(source):
    """Mask strings and nested Lean comments, preserving line boundaries."""
    result = []
    depth = 0
    in_string = False
    i = 0
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            if source[i] == "\\":
                result.extend("  ")
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
            continue
        if pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
            result.extend(" " * (end - i))
            i = end
        elif source[i] == '"':
            in_string = True
            result.append(" ")
            i += 1
        else:
            result.append(source[i])
            i += 1
    if depth or in_string:
        fail("unterminated comment or string in challenge")
    return "".join(result)


def check_challenge(source_path, config_path):
    if json.loads(config_path.read_text()) != EXPECTED_CONFIG:
        fail("configuration differs from the fixed main-theorem challenge")
    source = code_only(source_path.read_text())
    modules = []
    for line in source.splitlines():
        if not re.search(r"\bimport\b", line):
            continue
        match = re.fullmatch(r"\s*(?:public\s+)?import\s+(.+?)\s*", line)
        if not match:
            fail("unrecognized import syntax in challenge")
        for module in match.group(1).split():
            if not re.fullmatch(r"(?:Mathlib|MathlibExt)(?:\.[A-Za-z0-9_]+)*", module):
                fail("challenge imports non-external modules: " + module)
            modules.append(module)
    if not modules:
        fail("no external imports found")
    theorem_names = re.findall(
        r"(?m)^\s*(?:public\s+)?theorem\s+([A-Za-z0-9_'.]+)", source
    )
    if theorem_names != ["strict_threshold_unconditional"]:
        fail("challenge must contain only the main theorem")
    if len(re.findall(r"\bsorry\b", source)) != 1:
        fail("challenge must contain exactly one main-theorem placeholder")
    if re.search(r"\b(?:admit|native_decide|unsafe|implemented_by|extern)\b", source):
        fail("unsupported trust-expanding construct in challenge")
    if re.search(r"(?m)^\s*axiom\b", source):
        fail("challenge contains an extra axiom declaration")
    print("Challenge guard passed: external imports only; one main theorem and one placeholder")


def check_paths(project, full_path_file, output):
    project = project.resolve()
    manifest = project / "lake-manifest.json"
    if not manifest.is_file():
        fail("source project needs its pinned lake-manifest.json")
    data = json.loads(manifest.read_text())
    packages = data.get("packages", [])
    actual = {package["name"]: package["rev"] for package in packages}
    if len(actual) != len(packages) or actual != DEPENDENCY_PINS:
        fail("external dependency names or revisions differ from the verified pin")
    if data.get("packagesDir", ".lake/packages") != ".lake/packages":
        fail("unexpected dependency directory")
    allowed = {
        (project / ".lake/packages" / name / ".lake/build/lib/lean").resolve()
        for name in DEPENDENCY_PINS
    }
    own_build = (project / ".lake/build/lib/lean").resolve()
    accepted = []
    for spelling in full_path_file.read_text().strip().split(":"):
        if not spelling:
            fail("empty LEAN_PATH entry could expose the working directory")
        entry = Path(spelling)
        if not entry.is_absolute():
            fail("relative LEAN_PATH entry: " + spelling)
        entry = entry.resolve()
        if entry == own_build:
            continue
        if entry not in allowed:
            fail("non-external LEAN_PATH entry rejected: " + spelling)
        if not entry.is_dir():
            fail("dependency output directory does not exist: " + spelling)
        if str(entry) not in accepted:
            accepted.append(str(entry))
    if not accepted:
        fail("empty externals LEAN_PATH")
    mathlib = (project / ".lake/packages/mathlib/.lake/build/lib/lean").resolve()
    if str(mathlib) not in accepted:
        fail("the pinned Mathlib is not on the external search path")
    output.write_text(":".join(accepted) + "\n")
    print("Path guard passed: pinned external dependency outputs only")


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "challenge":
        check_challenge(Path(sys.argv[2]), Path(sys.argv[3]))
    elif len(sys.argv) == 5 and sys.argv[1] == "paths":
        check_paths(Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]))
    else:
        fail("usage: guard_inputs.py challenge SOURCE CONFIG | paths PROJECT FULL_PATH OUTPUT")


if __name__ == "__main__":
    main()
