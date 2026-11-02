#!/usr/bin/env python3
"""Assemble Papers/gaussian_ellipsoid_interactive.html (Atlas/Barei style).

Inputs (all paths relative to this file's directory, i.e. Papers/):
  prose_template.html   paper-first prose with <!--BOX:gNN--> placeholders
                        (derived once from the supplied manuscript rendering;
                        see derive_template.py) and a <!--LINKS--> placeholder
  inventory.json        48 assertion rows: paper titles + Lean declarations
  ../Formalization/     Lean sources (statements extracted + verified here)
  verification.json     separate build/axiom/coverage record, not rendered here
  assets/katex-0.16.11.offline.css
                        KaTeX stylesheet with 20 embedded font faces
  assets/katex.min.js + assets/auto-render.min.js
                        KaTeX 0.16.11 renderer (same bytes as the supplied
                        manuscript package and the Alpha Cycle reference)

The generated HTML includes every math script and all font data inline. It can
be opened offline without fetching a CDN or placing assets beside the HTML.
Papers/test_html_rendering.py checks these requirements and can additionally
require an actual offline Chromium render with --browser.

Usage:
  python3 generate_html.py            # regenerate the interactive HTML
  python3 generate_html.py --check    # fail unless the checked-in HTML is current

Every Lean box is statement-only (theorem proofs trimmed at the top-level
`:=` assignment, whether term-style or tactic-style; tactic-mode definition
bodies are trimmed too). Definitions with data bodies stay whole. Each box
includes file-level universe/variable context where the source declares any,
plus a blue `source` button under EACH declaration
linking to the real file + line range. Full texts sit in collapsed Technical
details. No coverage IDs, paper locators, KERNEL_CHECKED lines, or audit
internals appear in the boxes. Any drift between the inventory declarations
and Formalization/ is a hard error, never silently repaired.
"""

import html as htmlmod
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
FORM = os.path.join(PKG, "Formalization")

# Validated KaTeX macro expansions, copied from Latex/main.tex lines 53-73.
KATEX_MACROS = {
    "\\R": "\\mathbb{R}",
    "\\E": "\\mathbb{E}",
    "\\Pp": "\\mathbb{P}",
    "\\1": "\\boldsymbol{1}",
    "\\cA": "\\mathcal{A}",
    "\\cB": "\\mathcal{B}",
    "\\cF": "\\mathcal{F}",
    "\\cQ": "\\mathcal{Q}",
    "\\cT": "\\mathcal{T}",
    "\\PiZero": "\\Pi_n",
    "\\Sym": "\\operatorname{Sym}",
    "\\Tr": "\\operatorname{Tr}",
    "\\supp": "\\operatorname{supp}",
    "\\rank": "\\operatorname{rank}",
    "\\diag": "\\operatorname{diag}",
    "\\res": "\\operatorname{res}",
    "\\rvec": "\\operatorname{res}",
    "\\rentry": "\\operatorname{res}_{#1}",
    "\\op": "\\operatorname{op}",
    "\\Frob": "F",
    "\\whp": "\\text{with high probability }",
}

# Prose styles carried over from the supplied manuscript rendering
# (same rules, minus the draft-leanbox styles which the boxes below replace).
PROSE_CSS = """
:root {--bg:#fff;--fg:#252525;--muted:#666;--border:#ddd;--accent:#175d9d;--code:#f5f5f3}
@media(prefers-color-scheme:dark){:root{--bg:#151515;--fg:#ddd;--muted:#aaa;--border:#444;--accent:#8ab4ef;--code:#232323}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);font:17px/1.7 Georgia,'Times New Roman',serif}.page{display:flex;gap:2.5rem;max-width:1250px;margin:auto;padding:2rem 2rem 5rem}.toc{position:sticky;top:1.5rem;align-self:flex-start;flex:0 0 250px;max-height:93vh;overflow:auto;border-left:2px solid var(--border);padding-left:1rem;font:13px/1.5 Arial,sans-serif}.toc a{display:block;text-decoration:none;color:var(--muted);padding:.2rem 0}.toc a:hover{color:var(--accent)}.toc .toc-level-3{font-size:12px;padding-left:.8rem}main{min-width:0;max-width:820px}h1{font-size:1.65rem;line-height:1.35;text-align:center}h2{font-size:1.35rem;line-height:1.4;margin-top:2.6rem}h3{font-size:1.12rem;line-height:1.5;margin-top:2rem}h4{font-size:1rem}.authors,.reviewer{text-align:center}.reviewer{font-size:.9rem}.abstract{font-size:.95rem;margin:2rem 0}.links,.meta-note{font:13px/1.6 Arial,sans-serif;color:var(--muted)}a{color:var(--accent)}p{margin:.7rem 0}.env{margin:1.3rem 0}.env-label{font-weight:bold}.env.def{border-left:3px solid #3766aa;padding-left:.8rem}.env.exm{border-left:3px solid #888;padding-left:.8rem}.prov{border-left:2px solid #8ca8c4;padding-left:1rem;margin:1rem 0;position:relative}.prov.humanblock{border-left-color:#59a468}.prov-label{font:10px Arial,sans-serif;color:var(--muted);position:absolute;left:-1.1rem;top:.3rem;writing-mode:vertical-rl;transform:rotate(180deg)}.proof{margin:.8rem 0}.proof summary{cursor:pointer;font-style:italic;color:var(--accent)}.qed{text-align:right;font-size:.8rem}.source-anchor{scroll-margin-top:1rem}
@media(max-width:760px){.page{flex-direction:column;padding:1rem 1rem 4rem}.toc{position:static;flex:none;max-height:none;border-left:none;border-bottom:2px solid var(--border);padding:0 0 .6rem;margin-bottom:1rem}main{max-width:100%}}
"""

SUPPLEMENT_CSS = """
.prov-open{position:relative;border-left:2px solid var(--line,#8ca8c4);padding-left:1rem;margin:.6rem 0 1.2rem}
.meta-note{color:var(--muted);font-size:15px}
.citation{white-space:nowrap}
ul.refs{list-style:none;padding-left:0;font-size:15px}
ul.refs li{margin:.45rem 0;padding-left:4.6em;text-indent:-4.6em;overflow-wrap:anywhere}
.katex-display{max-width:100%;overflow-x:auto;overflow-y:hidden}
.katex-display>.katex{min-width:max-content}
.lean-box{border:1px solid var(--border);border-left:4px solid #258444;border-radius:4px;margin:1rem 0;font:13px/1.5 Arial,sans-serif}
.lean-box .decl-id{min-width:0;max-width:100%;white-space:normal;overflow-wrap:anywhere}
.lean-box>summary{list-style:none;cursor:pointer;display:flex;flex-wrap:wrap;gap:.35rem;align-items:baseline;padding:.7rem}
.lean-box>summary::-webkit-details-marker{display:none}
.lean-box>summary::before{content:"\\25B8";display:inline-block;flex:0 0 auto;color:var(--muted);margin-right:.4rem}
.lean-box[open]>summary::before{content:"\\25BE"}
.lean-box pre{overflow:auto;background:var(--code);padding:1rem;line-height:1.5;font-size:12px;margin:.4rem .7rem;white-space:pre-wrap;overflow-wrap:anywhere}
.lean-box pre.vars{background:transparent;border:1px dashed var(--border);font-size:11px;color:var(--muted)}
.lean-kind{display:block;text-transform:uppercase;color:var(--muted);font-size:11px}
.lean-title{font-weight:bold}
.lean-note{margin:0 .7rem 10px;font:13px/1.6 system-ui,sans-serif;color:#596975}
.srcline{text-align:right;padding:0 .8rem .4rem}
.srcline a{color:#fff;background:var(--accent);padding:.2rem .55rem;text-decoration:none;border-radius:4px}
details.proof{margin:.4rem 0 1.1rem}
details.tech-detail{margin:.2rem .7rem .8rem;font-size:12px}
details.tech-detail>summary{cursor:pointer;font-style:italic;display:inline;color:var(--blue,#175d9d)}
details.tech-detail .qed{text-align:right;font-size:1.3em;margin:0}
.reflabel{font-weight:bold}
"""


def fail(msg):
    raise SystemExit("generate_html: ERROR: " + msg)


DECLKIND = ("theorem", "lemma", "def", "abbrev", "structure", "instance",
            "example")


def module_relpath(module):
    if module.startswith("GaussianEllipsoid."):
        return "GaussianEllipsoid/%s.lean" % module.split(".", 1)[1]
    return "GaussianEllipsoidNative/%s.lean" % module


def scan_file_context(rel):
    """File-level universe/variable lines (verbatim) for the vars block."""
    ctx = []
    for ln in open(os.path.join(FORM, rel)).read().split("\n"):
        if re.match(r"^\s*(universe|variable)\b", ln):
            ctx.append(ln.rstrip())
    return ctx


def find_decl_in_file(rel, short, recorded_lo, recorded_hi):
    """Locate the declaration block, pinned by its recorded line range."""
    lines = open(os.path.join(FORM, rel)).read().split("\n")
    cands = []
    for i, ln in enumerate(lines):
        m = re.match(
            r"^(?:@\[.*?\] ?)?(?:public |private |noncomputable )?"
            r"(theorem|lemma|def|abbrev|structure|instance|example)"
            r"\s+([\w.']+)\b", ln)
        if m and (m.group(2) == short or m.group(2).endswith("." + short)):
            cands.append((i, m.group(1)))
    if not cands:
        fail("decl %s not declared in %s" % (short, rel))
    # prefer the candidate inside the recorded line window
    inside = [c for c in cands
              if recorded_lo - 3 <= c[0] + 1 <= recorded_hi + 3]
    if len(inside) != 1:
        fail("decl %s ambiguous in %s (candidates %s, recorded L%d-L%d)"
             % (short, rel, [c[0] + 1 for c in cands],
                recorded_lo, recorded_hi))
    i, kind = inside[0]
    start = i
    while start > 0 and (lines[start - 1].strip().startswith("/--")
                         or lines[start - 1].strip().startswith("@[")
                         or lines[start - 1].strip() == ""):
        prev = lines[start - 1].strip()
        if prev == "" or prev.startswith("/--") or prev.startswith("@["):
            start -= 1
        else:
            break
    end = i
    j = i
    n = len(lines)
    while j < n:
        s = lines[j]
        if j > i and s.strip() == "":
            q = j + 1
            while q < n and lines[q].strip() == "":
                q += 1
            if q >= n:
                end = j
                break
            nxt = lines[q]
            if re.match(
                    r"^(theorem|lemma|def|abbrev|structure|"
                    r"instance|example|namespace|end|section|"
                    r"@\[|/-|/--|#|import|open|variable|"
                    r"universe)", nxt):
                end = j - 1
                break
        end = j
        j += 1
    while end > start and lines[end].strip() == "":
        end -= 1
    return kind, "\n".join(lines[start:end + 1]), start + 1, end + 1


def top_level_assignment(code, include_where=False):
    """Locate a declaration body, ignoring defaults inside binders and comments."""
    stack = []
    comment_depth = 0
    in_string = False
    i = 0
    while i < len(code):
        pair = code[i:i + 2]
        if comment_depth:
            if pair == "/-":
                comment_depth += 1
                i += 2
            elif pair == "-/":
                comment_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_string:
            if code[i] == "\\":
                i += 2
            elif code[i] == '"':
                in_string = False
                i += 1
            else:
                i += 1
            continue
        if pair == "/-":
            comment_depth = 1
            i += 2
            continue
        if pair == "--":
            newline = code.find("\n", i)
            i = len(code) if newline < 0 else newline + 1
            continue
        if code[i] == '"':
            in_string = True
        elif code[i] in "([{":
            stack.append(code[i])
        elif code[i] in ")]}":
            if stack:
                stack.pop()
        elif pair == ":=" and not stack:
            return i
        elif include_where and not stack and code[i:i + 5] == "where":
            before = code[i - 1] if i else " "
            after = code[i + 5] if i + 5 < len(code) else " "
            if not (before.isalnum() or before == "_") and not (after.isalnum() or after == "_"):
                return i
        i += 1
    return None


def statement_of(full, kind):
    """Copy exact signatures; keep definition data, never theorem proof bodies."""
    code = re.sub(r"\A\s*/--.*?-/\s*\n", "", full, flags=re.S)
    assignment = top_level_assignment(code, include_where=True)
    if assignment is not None:
        body = code[assignment:]
        if kind in ("theorem", "lemma", "example") or re.search(r"\bby\b", body):
            return code[:assignment].rstrip()
    return code.rstrip()


def esc(s):
    return htmlmod.escape(s, quote=False)


def short_title(paper_title, label):
    t = (paper_title or "").strip()
    t = re.sub(r"^(Theorem|Lemma|Proposition|Corollary|Remark|Definition)"
               r"\s+[\d.]+\s*", "", t)
    t = t.strip()
    if t.startswith("(") and t.endswith(")"):
        t = t[1:-1]
    t = t.rstrip(".")
    return t or label


def build_box(row, decls):
    kind = row_kind(row, decls)
    title = short_title(row.get("paper_title", ""),
                        row.get("label") or row.get("claim", ""))
    decl_id = " \u00b7 ".join(d.split(".")[-1] for _, d, _, _, _, _, _, _
                             in decls)
    parts = []
    techs = []
    ctx_done = set()
    for (relpath, d, stmt, full, lo, hi, _kind, ctx) in decls:
        href = "../Formalization/%s#L%d-L%d" % (relpath, lo, hi)
        if ctx and relpath not in ctx_done:
            parts.append('<pre class="vars">%s</pre>'
                         % esc("\n".join(ctx)))
            ctx_done.add(relpath)
        parts.append("<pre>%s</pre>" % esc(stmt))
        parts.append(
            '<div class="srcline"><a href="%s">source</a></div>' % href)
        techs.append("<pre>%s</pre>" % esc(full))
    return (
        '<details class="lean-box checked"><summary>'
        '<span class="lean-kind">%s</span> '
        '<span class="lean-title">%s</span> '
        '<code class="decl-id">%s</code></summary>\n%s\n'
        '<details class="tech-detail"><summary>Technical details</summary>\n%s\n'
        "</details>\n</details>"
        % (esc(kind), esc(title), esc(decl_id), "".join(parts),
           "".join(techs)))


def row_kind(row, decls):
    if row.get("paper_kind"):
        return row["paper_kind"].capitalize()
    ks = [d[6] for d in decls]
    return (max(set(ks), key=ks.count).capitalize() if ks else "Assertion")


def extract_entry(name, link, ctx_cache):
    module = link["module"]
    recorded = link["lines"]
    rel = module_relpath(module)
    path = os.path.join(FORM, rel)
    if not os.path.exists(path):
        fail("source file missing: " + rel)
    short = name.split(".")[-1]
    kind, full, lo, hi = find_decl_in_file(rel, short, recorded[0],
                                           recorded[-1])
    if rel not in ctx_cache:
        ctx_cache[rel] = scan_file_context(rel)
    return rel, name, statement_of(full, kind), full, lo, hi, \
        kind, ctx_cache[rel]


def links_bar():
    return (
        '<p class="links"><a href="gaussian_ellipsoid.pdf">Paper PDF</a> | '
        '<a href="Latex/main.tex">Original LaTeX</a> | '
        '<a href="../Formalization/GaussianEllipsoid.lean">Lean library</a> | '
        '<a href="citation.bib">Citation</a></p>')


def shell_head():
    css_path = os.path.join(HERE, "assets/katex-0.16.11.offline.css")
    katex_css = open(css_path).read()
    if katex_css.count("@font-face") != 20:
        fail("offline KaTeX stylesheet must contain all 20 font-face rules")
    return (
        "<head><meta charset=\"utf-8\">"
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        "<title>The Strict Threshold for Gaussian Ellipsoid Fitting"
        " \u2014 formalized edition</title>"
        '<style id="katex-css">' + katex_css + "</style>"
        "<style>" + PROSE_CSS + SUPPLEMENT_CSS + "</style></head>")


def initializer_js():
    # json.dumps so every TeX backslash survives as a JS string escape.
    macros = json.dumps(KATEX_MACROS, indent=0)
    return (
        "document.addEventListener(\"DOMContentLoaded\",function(){"
        "renderMathInElement(document.body,{delimiters:["
        "{left:\"\\\\(\",right:\"\\\\)\",display:false},"
        "{left:\"\\\\[\",right:\"\\\\]\",display:true}],"
        "macros:" + macros + ",throwOnError:false});});")


def shell_tail():
    katex = open(os.path.join(HERE, "assets/katex.min.js")).read()
    autorender = open(os.path.join(HERE, "assets/auto-render.min.js")).read()
    if "renderMathInElement" not in autorender:
        fail("auto-render asset is not the KaTeX auto-renderer")
    return ("<script>" + katex + "</script>"
            "<script>" + autorender + "</script>"
            "<script>" + initializer_js() + "</script>"
            "</body></html>")


def assemble():
    inv = json.load(open(os.path.join(HERE, "inventory.json")))
    if len(inv) != 48:
        fail("inventory must hold all 48 assertion rows, found %d"
             % len(inv))
    entries_html = {}
    n_decls = 0
    ctx_cache = {}
    for row in inv:
        parts = []
        if len(row["declarations"]) != len(row.get("links", [])):
            fail("inventory links missing for box " + row["key"])
        for name, link in zip(row["declarations"], row["links"]):
            if link["name"] != name:
                fail("inventory link/name mismatch in box " + row["key"])
            parts.append(extract_entry(name, link, ctx_cache))
            n_decls += 1
        # box kind: paper env kind, else majority Lean declaration kind
        if not row.get("paper_kind"):
            ks = [p[6] for p in parts]
            row["paper_kind"] = max(set(ks), key=ks.count)
        entries_html[row["key"]] = build_box(row, parts)
    tpl = open(os.path.join(HERE, "prose_template.html")).read()
    for key, box_html in entries_html.items():
        ph = "<!--BOX:%s-->" % key
        if ph not in tpl:
            fail("placeholder missing in template: " + ph)
        tpl = tpl.replace(ph, box_html)
    if "<!--BOX:" in tpl:
        fail("unfilled box placeholders remain")
    if "<!--LINKS-->" not in tpl:
        fail("links placeholder missing in template")
    tpl = tpl.replace("<!--LINKS-->", links_bar())
    return ("<!DOCTYPE html><html>" + shell_head() + "<body>" + tpl
            + shell_tail()), n_decls


def main():
    check = len(sys.argv) > 1 and sys.argv[1] == "--check"
    out = os.path.join(HERE, "gaussian_ellipsoid_interactive.html")
    html, n_decls = assemble()
    if check:
        if not os.path.exists(out):
            fail("no checked-in HTML to compare against")
        cur = open(out).read()
        if cur != html:
            fail("--check: checked-in HTML differs from regenerated output; "
                 "run generate_html.py to refresh")
        print("generate_html --check: OK (%d declarations in 48 boxes)"
              % n_decls)
    else:
        open(out, "w").write(html)
        print("wrote %s (%d bytes, %d declarations in 48 boxes)"
              % (out, len(html), n_decls))


if __name__ == "__main__":
    main()
