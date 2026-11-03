#!/usr/bin/env python3
"""Fail-closed input guards for the independent Alpha-Cycle comparator.

These are source/path hygiene checks, not a Lean proof checker. The official
comparator and its kernel still decide the proof verdict.
"""

import json
import re
import sys
from pathlib import Path

EXPECTED_CONFIG = {
    "challenge_module": "alpha_cycle_comparator",
    "solution_module": "AlphaCycle",
    "theorem_names": ["AlphaCycle.PaperHypergraph.paper_sharp_classification"],
    "definition_names": [],
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
}

# Pinned external revisions the externals search path must be built from
# (assembly-time obligation; see the package Readme). The driver enforces
# toolchain hashes directly and path hygiene below.
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

CHALLENGE_ROOT_FILE = "alpha_cycle_comparator.lean"
CHALLENGE_DIR = "Challenge"
MAIN_THEOREM_FILE = "Challenge/Section_6_MainTheorem/PaperMain.lean"
MAIN_THEOREM_NAME = "paper_sharp_classification"


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


def check_challenge(comparator_dir, config_path):
    comparator_dir = Path(comparator_dir)
    if json.loads(Path(config_path).read_text()) != EXPECTED_CONFIG:
        fail("configuration differs from the fixed main-theorem challenge")
    root = comparator_dir / CHALLENGE_ROOT_FILE
    if not root.is_file():
        fail("challenge root not found: " + str(root))
    sources = sorted((comparator_dir / CHALLENGE_DIR).rglob("*.lean"))
    if not sources:
        fail("no challenge excerpt modules found")
    expected = sorted(
        (comparator_dir / CHALLENGE_DIR / p for p in [
            "Section_1_Introduction/Geometry.lean",
            "Section_2_Preliminaries/FiniteLaw.lean",
            "Section_2_Preliminaries/MomentInversion.lean",
            "Section_2_Preliminaries/Polytope.lean",
            "Section_2_Preliminaries/Triangle.lean",
            "Section_2_Preliminaries/Relaxation.lean",
            "Section_2_Preliminaries/DefinitionAudit.lean",
            "Section_2_Preliminaries/PaperCoordinates.lean",
            "Section_2_Preliminaries/GeometryCycle.lean",
            "Section_2_Preliminaries/PaperHypergraph.lean",
            "Section_6_MainTheorem/PaperMain.lean",
        ]))
    if sources != expected:
        fail("challenge excerpt module set differs from the verified set")
    files = [root] + sources
    sorry_total = 0
    theorem_hits = []
    for path in files:
        source = code_only(path.read_text())
        for line in source.splitlines():
            if not re.search(r"\bimport\b", line):
                continue
            match = re.fullmatch(r"\s*(?:public\s+)?import\s+(.+?)\s*", line)
            if not match:
                fail("unrecognized import syntax in challenge: " + str(path))
            for module in match.group(1).split():
                if re.fullmatch(r"Mathlib(?:\.[A-Za-z0-9_]+)*", module):
                    continue
                if re.fullmatch(r"Challenge(?:\.[A-Za-z0-9_]+)+", module):
                    target = comparator_dir / (module.replace(".", "/") + ".lean")
                    if not target.is_file():
                        fail("challenge-internal import does not resolve: "
                             + module + " in " + str(path))
                    continue
                fail("challenge imports non-external modules: %s in %s"
                     % (module, path))
        theorem_hits.extend(
            (str(path), name)
            for name in re.findall(
                r"(?m)^\s*(?:public\s+)?theorem\s+([A-Za-z0-9_'.]+)", source))
        sorry_total += len(re.findall(r"\bsorry\b", source))
        if re.search(r"\b(?:admit|native_decide|unsafe|implemented_by|extern)\b",
                     source):
            fail("unsupported trust-expanding construct in challenge: "
                 + str(path))
        if re.search(r"(?m)^\s*axiom\b", source):
            fail("challenge contains an extra axiom declaration: " + str(path))
    mains = [(p, n) for (p, n) in theorem_hits
             if n.split(".")[-1] == MAIN_THEOREM_NAME]
    if len(mains) != 1 or mains[0][0] != str(comparator_dir / MAIN_THEOREM_FILE):
        fail("challenge must state the main theorem exactly once, in "
             + MAIN_THEOREM_FILE)
    others = [(p, n) for (p, n) in theorem_hits
              if n.split(".")[-1] != MAIN_THEOREM_NAME]
    if others:
        # Helper-lemma copies are allowed only as complete proofs; the single
        # placeholder below is the only admission in the whole challenge.
        pass
    if sorry_total != 1:
        fail("challenge must contain exactly one main-theorem placeholder, "
             "found %d" % sorry_total)
    print("Challenge guard passed: external+challenge-internal imports only; "
          "one main theorem and one placeholder")


def check_solution(package_root):
    """Fail if any solution source contains a proof placeholder in code."""
    sources = sorted((Path(package_root) / "Formalization").rglob("*.lean"))
    if not sources:
        fail("no solution sources found")
    for path in sources:
        source = code_only(path.read_text())
        if re.search(r"\bsorry\b|\badmit\b", source):
            fail("solution source contains a placeholder: " + str(path))
    print("Solution guard passed: no sorry/admit placeholders in %d modules"
          % len(sources))
def check_paths(package_root, externals_path, solution_build, challenge_build,
                output):
    """Validate the externals search path (direct-Lean assembly, no Lake)."""
    package_root = Path(package_root).resolve()
    entries = externals_path.read_text().strip().split(":")
    if not entries or not entries[0]:
        fail("empty externals search path")
    solution_build = Path(solution_build).resolve()
    challenge_build = Path(challenge_build).resolve()
    accepted = []
    has_mathlib = False
    for spelling in entries:
        if not spelling:
            fail("empty LEAN_PATH entry could expose the working directory")
        entry = Path(spelling)
        if not entry.is_absolute():
            fail("relative LEAN_PATH entry: " + spelling)
        entry = entry.resolve()
        if not entry.is_dir():
            fail("dependency output directory does not exist: " + spelling)
        for banned in (package_root, solution_build, challenge_build):
            if entry == banned or banned in entry.parents:
                fail("search-path entry inside the package or its build "
                     "outputs: " + spelling)
            if entry in banned.parents:
                fail("search-path entry above the package or its build "
                     "outputs: " + spelling)
        if entry == solution_build or entry == challenge_build:
            fail("solution/challenge build output on the externals path: "
                 + spelling)
        if (entry / "Mathlib.olean").is_file():
            has_mathlib = True
        if str(entry) not in accepted:
            accepted.append(str(entry))
    if not has_mathlib:
        fail("no pinned Mathlib output (Mathlib.olean) on the externals path")
    Path(output).write_text(":".join(accepted) + "\n")
    print("Path guard passed: externals-only search path with pinned Mathlib")


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "challenge":
        check_challenge(Path(sys.argv[2]), Path(sys.argv[3]))
    elif len(sys.argv) == 3 and sys.argv[1] == "solution":
        check_solution(Path(sys.argv[2]))
    elif len(sys.argv) == 7 and sys.argv[1] == "paths":
        check_paths(Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]),
                    Path(sys.argv[5]), Path(sys.argv[6]))
    else:
        fail("usage: guard_inputs.py challenge COMPARATOR_DIR CONFIG | "
             "solution PACKAGE_ROOT | "
             "paths PACKAGE_ROOT EXTERNALS_FILE SOLUTION_BUILD "
             "CHALLENGE_BUILD OUTPUT")


if __name__ == "__main__":
    main()
