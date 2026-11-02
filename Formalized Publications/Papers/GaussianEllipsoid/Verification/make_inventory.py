#!/usr/bin/env python3
"""Build Verification/inventory.json from Papers/inventory.json.

The JSON is the 48-row verification inventory (40 named + 8 supplemental):
every row carries its paper reference and all Lean declaration bindings with
resolved file paths. Re-running must be byte-identical.

This inventory is a verification aid, not the Atlas challenge config; the
challenge config is Comparator/gaussian_ellipsoid_comparator.json.

Usage:
  python3 Verification/make_inventory.py
"""

import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def mod_path(module):
    if module.startswith("GaussianEllipsoid."):
        return "Formalization/GaussianEllipsoid/%s.lean" % module.split(".", 1)[1]
    return "Formalization/GaussianEllipsoidNative/%s.lean" % module


def main():
    inv = json.load(open(os.path.join(HERE, "..", "Papers", "inventory.json")))
    rows = []
    for row in inv:
        bindings = []
        for link in row["links"]:
            bindings.append({"declaration": link["name"],
                             "module": link["module"],
                             "file": mod_path(link["module"]),
                             "recorded_lines": link["lines"]})
        entry = {"box": row["key"],
                 "paper": (row.get("label")
                           or row.get("paper_title")
                           or row.get("claim", "")),
                 "supplemental": bool(row["supplemental"]),
                 "paper_span": row.get("paper_span", []),
                 "display_line": row.get("display_line"),
                 "bindings": bindings}
        rows.append(entry)
    out = {"audit_module": "EndpointAudit",
           "solution_module": "GaussianEllipsoid",
           "kind": "verification-only inventory (audits the solution; not an "
                   "independent challenge file)",
           "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
           "endpoint_names": [
               "GaussianEllipsoid.strict_threshold_unconditional",
               "GaussianEllipsoid.below_threshold_unconditional",
               "GaussianEllipsoid.mixedNormBound_unconditional",
               "GaussianEllipsoid.bmApproximateFitting_unconditional",
               "GaussianEllipsoid.uniformConicBound_unconditional",
               "AHHRadial.paper_equation11"],
           "rows": rows}
    path = os.path.join(HERE, "inventory.json")
    open(path, "w").write(json.dumps(out, indent=1) + "\n")
    n = sum(len(r["bindings"]) for r in rows)
    print("wrote %s (%d rows, %d bindings)" % (path, len(rows), n))


if __name__ == "__main__":
    main()
