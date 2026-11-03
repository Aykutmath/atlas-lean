#!/usr/bin/env python3
"""Check that every requested export root resolves in an export34 NDJSON file.

Usage: check_exports.py <ndjson> <root1> <root2> ...
Exit 0 iff every root name resolves through the file's interned name table.
(This is a completeness check on serializer output, not a proof check.)
"""

import json
import sys


def main():
    path, roots = sys.argv[1], sys.argv[2:]
    raw = {}
    with open(path) as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except ValueError:
                print("export is not line-delimited JSON")
                return 1
            if "in" in obj and ("str" in obj or "num" in obj):
                raw[obj["in"]] = obj
    names = {0: ""}
    numeric = {}

    def resolve(i):
        if i in names:
            return names[i]
        obj = raw.get(i)
        if obj is None:
            raise KeyError(i)
        if "str" in obj:
            s = obj["str"]
            names[i] = resolve(s["pre"]) + "." + s["str"] \
                if resolve(s["pre"]) else s["str"]
        else:
            s = obj["num"]
            names[i] = resolve(s["pre"]) + "." + str(s["i"])
        return names[i]

    try:
        resolved = {resolve(i) for i in raw}
    except KeyError as exc:
        print("export name table is incomplete, missing id %s" % (exc,))
        return 1
    missing = [r for r in roots if r not in resolved]
    if missing:
        print("export roots missing from NDJSON: %s" % ", ".join(missing))
        return 1
    print("export roots present: %d/%d" % (len(roots), len(roots)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
