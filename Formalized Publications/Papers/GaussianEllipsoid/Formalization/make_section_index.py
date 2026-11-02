#!/usr/bin/env python3
"""Generate Section_*/README.md entrypoints + FILE_MAP.md from inventory.

Reads Papers/inventory.json (48 rows with paper titles + declaration links)
and writes paper-order index folders under Formalization/. Re-running must
be byte-identical.

Usage:
  python3 Formalization/make_section_index.py
"""

import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))

SECTION_NAMES = {
    1: "Introduction",
    4: "RobustLoss",
    5: "SmallBall",
    6: "LocalizedEstimate",
    7: "MultiscaleEstimate",
    8: "BilinearBlock",
    9: "UniformSmallCoordinate",
    10: "ClippedHead",
    11: "ExactCorrection",
    12: "QuotientDuality",
    13: "InfeasibilityAbove",
    14: "CavityComparison",
    15: "DiffuseRestatement",
    16: "FullPSD",
}


def mod_path(module):
    if module.startswith("GaussianEllipsoid."):
        return "GaussianEllipsoid/%s.lean" % module.split(".", 1)[1]
    return "GaussianEllipsoidNative/%s.lean" % module


def main():
    inv = json.load(open(os.path.join(HERE, "..", "Papers",
                                      "inventory.json")))
    sections = {}
    for row in inv:
        if row["supplemental"]:
            sec = 8  # AHH displays sit in the section 8 bilinear-block proof
        else:
            m = re.match(r"^(Theorem|Lemma|Proposition|Corollary|Remark)"
                         r"\s+(\d+)\.", row["label"])
            if not m:
                raise SystemExit("cannot section row " + row["key"])
            sec = int(m.group(2))
        sections.setdefault(sec, []).append(row)
    for sec in sorted(sections):
        name = "Section_%02d_%s" % (sec, SECTION_NAMES[sec])
        d = os.path.join(HERE, name)
        os.makedirs(d, exist_ok=True)
        lines = ["# Section %d (%s)" % (sec, SECTION_NAMES[sec]), "",
                 "Paper-order entrypoint: the Lean modules behind this "
                 "section's inventory rows. Namespaces and theorem names "
                 "are unchanged; only the package prefix is new.", ""]
        for row in sections[sec]:
            title = row.get("paper_title") or row.get("claim", "")
            ref = row.get("label") or ("display line %d"
                                       % row.get("display_line", 0))
            lines.append("## %s — %s" % (ref, title))
            lines.append("")
            for link in row["links"]:
                lines.append("- `%s` in [%s](../%s)"
                             % (link["name"], mod_path(link["module"]),
                                mod_path(link["module"])))
            lines.append("")
        open(os.path.join(d, "README.md"), "w").write("\n".join(lines))
    print("wrote %d section indexes" % len(sections))

    # old -> new file map (mechanical prefix change; bytes unchanged)
    rows = ["# Old-to-new file map", "",
            "The proof package actually moved: "
            "`agents/gaussian-ellipsoid/<path>` became "
            "`src/gaussian-ellipsoid/Formalization/<path>` with identical "
            "bytes (frozen ledger `SOURCES_SHA256.txt`, verified by "
            "`check_preservation.py`; no import line touched). "
            "New files added by this reformat: "
            "`Formalization/GaussianEllipsoid.lean` (root), "
            "`SOURCES_SHA256.txt`, "
            "`Section_*/README.md`, `FILE_MAP.md`, `check_preservation.py`, "
            "`make_section_index.py`.", ""]
    for sub in ("GaussianEllipsoid", "GaussianEllipsoidNative"):
        d = os.path.join(HERE, sub)
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".lean"):
                rows.append("- `%s/%s` ← `agents/gaussian-ellipsoid/%s/%s`"
                            % (sub, fn, sub, fn))
    rows.append("- `GaussianEllipsoid.lean` ← new (root entry point)")
    open(os.path.join(HERE, "FILE_MAP.md"), "w").write("\n".join(rows) + "\n")
    print("wrote FILE_MAP.md")


if __name__ == "__main__":
    main()
