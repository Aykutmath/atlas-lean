#!/usr/bin/env python3
"""One-time derivation of Papers/prose_template.html + Papers/inventory.json.

Input (NOT checked in; supplied provenance only):
  the manuscript rendering projects/arslan/docs/gaussian-ellipsoid/paper.html
  from arslan_gaussian_ellipsoid_for_kep_stem_math.zip
  (pandoc conversion of the authoritative paper.tex, sha256 2b8bec75...e37).

Run once from this directory:
  python3 derive_template.py /path/to/paper.html

What it does:
  - drops every old <details class="leanbox ..."> draft box,
  - drops the old status banner, old links bar (rewritten), source transcript,
    footer note and TOC transcript link,
  - converts pandoc <span class="math inline/display">TeX</span> to
    \\(...\\) / \\[...\\] for the offline KaTeX auto-renderer,
  - inserts <!--BOX:gNN--> placeholders at the 48 coverage-mapped anchors
    (40 named LEAN-AFTER markers + 8 supplemental display-line anchors),
  - writes inventory.json (box order, paper titles, Lean declaration lists)
    from GaussianEllipsoid_FINAL_Coverage.json in the agents source folder.

The outputs prose_template.html + inventory.json are the checked-in,
reviewed generator inputs. Re-running must be byte-identical.
"""

import html as htmlmod
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
COVERAGE = os.path.normpath(os.path.join(
    HERE, "..", "..", "..", "agents", "gaussian-ellipsoid",
    "GaussianEllipsoid_FINAL_Coverage.json"))

# coverage id -> marker id used in paper.html
MARKER_ALIAS = {"unlabeled-remark-1867": "remark-L1867"}


def fail(msg):
    raise SystemExit("derive_template: ERROR: " + msg)


def load_coverage():
    cov = json.load(open(COVERAGE))
    links = {}
    for l in cov["declaration_links"]:
        links[l["name"]] = {"module": l["module"],
                            "lines": list(l["source_lines"])}
    rows = []
    for s in cov["named_statements"]:
        rows.append({"id": s["id"], "label": s.get("label", ""),
                     "span": tuple(s["paper_span"]),
                     "declarations": list(s["declarations"]),
                     "supplemental": False})
    for s in cov["supplemental_displays"]:
        rows.append({"id": None, "label": "", "span": None,
                     "display": s["display"], "claim": s["claim"],
                     "declarations": list(s["declarations"]),
                     "supplemental": True})
    return rows, links


def strip_old_boxes(t):
    n0 = len(re.findall(r'<details class="leanbox', t))
    t = re.sub(r'<details class="leanbox.*?</details>', "", t, flags=re.S)
    # old per-line markers (kept: only the 40 id markers, handled later)
    t = re.sub(r"<!--LEAN-AFTER-LINE:\d+-->", "", t)
    return t, n0


def convert_math(t):
    """pandoc math spans -> KaTeX delimiters. Returns (text, n_inline, n_display)."""
    counts = {"i": 0, "d": 0}

    def rep_inline(m):
        counts["i"] += 1
        code = htmlmod.unescape(m.group(1))
        if re.search(r"</?[a-zA-Z][a-zA-Z0-9]*(?:\s[^<>]*)?>", code):
            fail("unexpected markup inside inline math: " + code[:80])
        # re-escape for HTML text (pandoc had &lt;/&gt;/&amp; here); the
        # browser restores them before KaTeX sees the formula.
        return "\\(" + htmlmod.escape(code.strip(), quote=False) + "\\)"

    def rep_display(m):
        counts["d"] += 1
        code = htmlmod.unescape(m.group(1))
        if re.search(r"</?[a-zA-Z][a-zA-Z0-9]*(?:\s[^<>]*)?>", code):
            fail("unexpected markup inside display math: " + code[:80])
        return "\\[" + htmlmod.escape(code.strip(), quote=False) + "\\]"

    t = re.sub(r'<span\s+class="math inline">(.*?)</span>', rep_inline, t,
               flags=re.S)
    t = re.sub(r'<span\s+class="math display">(.*?)</span>', rep_display, t,
               flags=re.S)
    if 'class="math' in t:
        fail("unconverted math spans remain")
    return t, counts["i"], counts["d"]


def main():
    if len(sys.argv) != 2:
        fail("usage: python3 derive_template.py /path/to/paper.html")
    src = open(sys.argv[1]).read()
    rows, links = load_coverage()
    for row in rows:
        missing = [d for d in row["declarations"] if d not in links]
        if missing:
            fail("declarations without module links: %s" % missing)
        row["links"] = [dict(name=d, **links[d]) for d in row["declarations"]]

    t, n_old = strip_old_boxes(src)
    print("removed old lean boxes: %d" % n_old)

    # Drop supplied-page annotations; verification records stay separate.
    t, n = re.subn(r'<div class="status-note">.*?</div>', "", t, flags=re.S)
    print("removed status banners: %d" % n)
    t, n = re.subn(r'<p class="links">.*?</p>', "<!--LINKS-->", t, flags=re.S)
    print("rewrote links bar: %d" % n)
    t, n = re.subn(r'<a href="#source-transcript">Source transcript</a>', "",
                   t)
    print("removed transcript TOC link: %d" % n)
    i = t.find('<details id="source-transcript"')
    if i < 0:
        fail("transcript block not found")
    j = t.find("</main>", i)
    if j < 0:
        fail("no </main> after transcript")
    t = t[:i] + t[j:]
    print("cut transcript block (%d bytes)" % (j - i))
    t, n = re.subn(r'<footer class="meta-note">.*?</footer>', "", t,
                   flags=re.S)
    print("removed footer notes: %d" % n)

    t, n_inline, n_display = convert_math(t)
    print("math converted: %d inline, %d display" % (n_inline, n_display))

    # Insert placeholders at coverage anchors; collect env titles.
    inventory = []
    for idx, row in enumerate(rows):
        key = "g%02d" % idx
        if not row["supplemental"]:
            marker = "<!--LEAN-AFTER:%s-->" % MARKER_ALIAS.get(row["id"],
                                                              row["id"])
            if marker not in t:
                fail("marker missing: " + marker)
            env = env_before(t, t.find(marker))
            kind, title = env
            t = t.replace(marker, "<!--BOX:%s-->" % key, 1)
            inventory.append({"key": key, "id": row["id"],
                              "label": row["label"],
                              "paper_kind": kind, "paper_title": title,
                              "paper_span": list(row["span"]),
                              "supplemental": False,
                              "claim": "",
                              "declarations": row["declarations"],
                              "links": row["links"]})
        else:
            anchor = ('<span class="source-anchor" id="paper-L%d"></span>'
                      % row["display"])
            placed = row["display"]
            if anchor not in t:
                # No per-line anchor inside long un-fragmented prose
                # (e.g. the bilinear-block proof): fall back to the next
                # source anchor after the display line, keeping paper order.
                nxt = None
                for m in re.finditer(
                        r'<span class="source-anchor" '
                        r'id="paper-L(\d+)"></span>', t):
                    if int(m.group(1)) > row["display"]:
                        nxt = m
                        break
                if nxt is None:
                    fail("display anchor missing: paper-L%d" % row["display"])
                anchor = nxt.group(0)
                placed = int(nxt.group(1))
                print("supplemental display %d placed at next anchor L%d"
                      % (row["display"], placed))
            t = t.replace(anchor,
                          "<!--BOX:%s-->" % key + anchor, 1)
            inventory.append({"key": key, "id": None, "label": "",
                              "paper_kind": "", "paper_title": "",
                              "paper_span": [],
                              "supplemental": True,
                              "claim": row["claim"],
                              "display_line": row["display"],
                              "placed_at_anchor_line": placed,
                              "declarations": row["declarations"],
                              "links": row["links"]})
    if "<!--LEAN-AFTER:" in t:
        fail("unfilled LEAN-AFTER markers remain")

    # Keep only the page div (drop old head/body shell); generator owns it.
    b = t.find('<div class="page">')
    if b < 0:
        fail("no page div")
    e = t.find("</main>", b)
    body = t[b:e + len("</main>")] + "</div>"
    # sanity: no remote URLs, no leftover audit text in prose
    for pat in ("https://github.com/metainternal", "http://",
                "READY_FOR_COMPILATION", "KERNEL_CHECKED", "Coverage ID",
                "Paper locator", "source unpublished",
                "Lean declaration"):
        if pat in body and pat != "http://":
            fail("unwanted residue in template prose: " + pat)
    if "https://" in body:
        bad = sorted(set(re.findall(r"https://[^\"'<> ]+", body)))
        fail("remote URLs remain in template prose: %s" % bad[:5])

    tpl_path = os.path.join(HERE, "prose_template.html")
    open(tpl_path, "w").write(body)
    inv_path = os.path.join(HERE, "inventory.json")
    open(inv_path, "w").write(json.dumps(inventory, indent=1) + "\n")
    print("wrote %s (%d bytes, 48 boxes)" % (tpl_path, len(body)))
    print("wrote %s (%d rows)" % (inv_path, len(inventory)))

    # macro hygiene: every custom TeX command in the prose must be KaTeX-safe
    cmds = set(re.findall(r"\\([a-zA-Z]+)", body))
    print("distinct TeX commands in prose: %d" % len(cmds))
    open("/tmp/gaussian_prose_cmds.txt", "w").write("\n".join(sorted(cmds)))


def env_before(t, pos):
    """Nearest paper environment section starting before pos."""
    best = None
    for m in re.finditer(
            r'<section class="env[^"]*" id="([^"]+)" '
            r'data-paper-kind="([^"]+)">'
            r'<div class="env-label">(.*?)</div>', t):
        if m.start() < pos:
            best = m
        else:
            break
    if best is None:
        return "", ""
    kind = best.group(2)
    title = re.sub(r"<[^>]+>", "", best.group(3)).strip()
    return kind, title


if __name__ == "__main__":
    main()
