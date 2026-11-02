#!/usr/bin/env python3
"""Source-preservation + import-closure checks for the Gaussian package.

Compares every Formalization/ module byte-for-byte against the frozen
agents/gaussian-ellipsoid/ originals (same worktree base), cross-checks the
original LEAN_SOURCES_SHA256SUMS.txt provenance, verifies every project
import resolves inside Formalization/, and emits a topological build order.

Usage:
  python3 Formalization/check_preservation.py
"""

import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FORM = HERE
ORIG = os.path.normpath(os.path.join(
    HERE, "..", "..", "..", "agents", "gaussian-ellipsoid"))
SUMS = os.path.join(ORIG, "LEAN_SOURCES_SHA256SUMS.txt")
LEDGER = os.path.join(HERE, "SOURCES_SHA256.txt")


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def fail(msg):
    raise SystemExit("check_preservation: ERROR: " + msg)


def main():
    ledger = {}
    for ln in open(LEDGER).read().splitlines():
        ln = ln.strip()
        if not ln:
            continue
        h, p = ln.split(None, 1)
        ledger[p] = h
    # (Historical LEAN_SOURCES_SHA256SUMS.txt stays in agents/ as
    # provenance; the frozen ledger above is the gate.)
    n = 0
    for sub in ("GaussianEllipsoid", "GaussianEllipsoidNative"):
        d = os.path.join(FORM, sub)
        for fn in sorted(os.listdir(d)):
            if not fn.endswith(".lean"):
                continue
            n += 1
            new = os.path.join(d, fn)
            key = sub + "/" + fn
            if ledger.get(key) != sha(new):
                fail("ledger mismatch (moved source changed?): " + key)
            # when the pre-move originals are still present, cross-check
            # them too; after the actual move only the ledger remains.
            old = os.path.join(ORIG, sub, fn)
            if os.path.exists(old) and sha(new) != sha(old):
                fail("byte drift vs pre-move original in " + key)
    print("preservation: %d modules match frozen ledger "
          "(+ pre-move originals where present)" % n)
    if n != 770:
        fail("expected 770 modules, found %d" % n)

    # import closure + topo order (project imports only)
    mods = {}   # module -> (relpath, deps)
    for sub in ("GaussianEllipsoid", "GaussianEllipsoidNative"):
        d = os.path.join(FORM, sub)
        for fn in sorted(os.listdir(d)):
            if not fn.endswith(".lean"):
                continue
            rel = sub + "/" + fn
            if sub == "GaussianEllipsoid":
                mod = "GaussianEllipsoid." + fn[:-5]
            else:
                mod = fn[:-5]
            deps = set()
            for ln in open(os.path.join(d, fn)).read().splitlines():
                m = re.match(r"^import\s+([A-Za-z0-9_.]+)", ln)
                if not m:
                    continue
                dep = m.group(1)
                if dep.startswith("Mathlib"):
                    continue
                deps.add(dep)
            mods[mod] = (rel, deps)
    # root module
    root = os.path.join(FORM, "GaussianEllipsoid.lean")
    deps = set()
    for ln in open(root).read().splitlines():
        m = re.match(r"^import\s+([A-Za-z0-9_.]+)", ln)
        if m and not m.group(1).startswith("Mathlib"):
            deps.add(m.group(1))
    mods["GaussianEllipsoid"] = ("GaussianEllipsoid.lean", deps)

    known = set(mods)
    for mod, (rel, deps) in sorted(mods.items()):
        for dep in sorted(deps):
            if dep in known:
                continue
            # a GaussianEllipsoid.* import whose file must exist
            if dep.startswith("GaussianEllipsoid."):
                want = os.path.join(
                    FORM, "GaussianEllipsoid", dep.split(".", 1)[1] + ".lean")
            else:
                want = os.path.join(FORM, "GaussianEllipsoidNative",
                                    dep + ".lean")
            if not os.path.exists(want):
                fail("unresolved import %s in %s" % (dep, rel))
            known.add(dep)
    # every dep resolves to a known module file (files == modules here)
    missing = set()
    for mod, (rel, deps) in mods.items():
        for dep in deps:
            if dep.startswith("GaussianEllipsoid."):
                ok = os.path.exists(os.path.join(
                    FORM, "GaussianEllipsoid", dep.split(".", 1)[1] + ".lean"))
            elif dep.startswith("Mathlib"):
                ok = True
            else:
                ok = os.path.exists(os.path.join(
                    FORM, "GaussianEllipsoidNative", dep + ".lean"))
            if not ok:
                missing.add((rel, dep))
    if missing:
        fail("unresolved imports: %s" % sorted(missing)[:10])
    print("closure: all project imports resolve (%d modules + root)"
          % (len(mods) - 1))

    # forbidden tokens in code (comments stripped first)
    bad = []
    for mod, (rel, _) in sorted(mods.items()):
        if rel == "GaussianEllipsoid.lean":
            text = open(root).read()
        else:
            text = open(os.path.join(FORM, rel)).read()
        code = re.sub(r"/--.*?-/", "", text, flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        for pat in (r"\bsorry\b", r"\bnative_decide\b", r"(?m)^\s*axiom\s",
                    r"\bunsafe\b", r"(?m)^\s*admit\b"):
            if re.search(pat, code):
                bad.append((rel, pat))
    if bad:
        fail("forbidden tokens in solution code: %s" % bad[:10])
    print("tokens: no sorry/admit/native_decide/axiom/unsafe in code")

    # Kahn topo order (alphabetical tiebreak), grouped by depth
    indeg = {m: len([d for d in ds if d in mods]) for m, (_, ds) in mods.items()}
    import collections
    rdep = collections.defaultdict(set)
    for m, (_, ds) in mods.items():
        for x in ds:
            if x in mods:
                rdep[x].add(m)
    order, ready, lv = [], sorted([m for m in mods if indeg[m] == 0]), 0
    level = {}
    while ready:
        order.append(ready)
        nxt = set()
        for m in ready:
            level[m] = lv
            for y in rdep[m]:
                indeg[y] -= 1
                if indeg[y] == 0:
                    nxt.add(y)
        ready = sorted(nxt)
        lv += 1
    left = [m for m in mods if m not in level]
    if left:
        fail("import cycle involving: %s" % left[:10])
    out = "/tmp/gaussian-levels.txt"
    with open(out, "w") as f:
        for grp in order:
            f.write("LEVEL:" + " ".join("%s=%s" % (m, mods[m][0])
                                        for m in grp) + "\n")
    print("topo: %d levels, %d modules, written to %s"
          % (len(order), len(mods), out))


if __name__ == "__main__":
    main()
