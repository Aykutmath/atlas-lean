#!/usr/bin/env python3
"""Assemble Papers/alpha_cycle_interactive.html (Barei style) from checked-in inputs.

Inputs (all paths relative to this file's directory, i.e. Papers/):
  prose_template.html   paper-first prose with <!--BOX:boxN--> placeholders
  ../Formalization/     Lean sources (statements extracted + verified here)
  lean_boxes_manifest.json
                        committed fidelity baseline: the 19 verified Lean box
                        statements (derived 2026-11-02 from the Nov-1 verified
                        HTML edition, itself checked box-for-box against the
                        previous prose rendering). Every regenerated statement
                        must equal its manifest entry exactly, and occur
                        verbatim in the Formalization/ sources.
  assets/katex-0.16.11.offline.css
                        repaired KaTeX stylesheet with 20 embedded font faces
  assets/shell_prefix.html
                        vendored document head (doctype, meta, title, donor
                        stylesheet) shared with the Nov-1 verified edition
  assets/shell_scripts.html
                        vendored trailing scripts (KaTeX library, auto-render
                        library and equation-rendering initializer)

The generated HTML includes every math script and all font data inline. It can
be opened offline without fetching a CDN or placing assets beside the HTML.
Papers/test_html_rendering.py checks these requirements and can additionally
require an actual offline Chromium render with --browser.

Usage:
  python3 generate_html.py            # regenerate alpha_cycle_interactive.html
  python3 generate_html.py --check    # fail unless the checked-in HTML is current

Every Lean box is statement-only (theorem/lemma proofs trimmed at `:= by`;
definitions shown whole) with a blue `source` button per entry linking to the
real file + line range. Full texts sit in collapsed Technical details. No
coverage IDs, paper locators, KERNEL_CHECKED lines, or audit internals appear
in the boxes. Any drift between the manifest statements and Formalization/ is
a hard error, never silently repaired. Verification records (build, axioms,
coverage, comparator) live in Papers/verification.json and Comparator/
Verification/, not in the paper prose; References is the final section.
"""

import html as htmlmod
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
FORM = os.path.join(PKG, "Formalization")
MANIFEST_JSON = os.path.join(HERE, "lean_boxes_manifest.json")
SHELL_PREFIX = os.path.join(HERE, "assets/shell_prefix.html")
SHELL_SCRIPTS = os.path.join(HERE, "assets/shell_scripts.html")

SECTION_OF_FILE = {
    "Geometry": "Section_1_Introduction",
    "FiniteLaw": "Section_2_Preliminaries",
    "Basic": "Section_2_Preliminaries",
    "Core": "Section_2_Preliminaries",
    "MomentInversion": "Section_2_Preliminaries",
    "MomentConverse": "Section_2_Preliminaries",
    "PaperInversionIdentities": "Section_2_Preliminaries",
    "PaperTranscription": "Section_2_Preliminaries",
    "Polytope": "Section_2_Preliminaries",
    "Triangle": "Section_2_Preliminaries",
    "Relaxation": "Section_2_Preliminaries",
    "AllCycles": "Section_2_Preliminaries",
    "CyclePermutation": "Section_2_Preliminaries",
    "LocalVector": "Section_2_Preliminaries",
    "PaperCoordinates": "Section_2_Preliminaries",
    "PaperHypergraph": "Section_2_Preliminaries",
    "PaperGeometry": "Section_2_Preliminaries",
    "PaperCycleCorrespondence": "Section_2_Preliminaries",
    "PaperTriangles": "Section_2_Preliminaries",
    "DefinitionAudit": "Section_2_Preliminaries",
    "Reindex": "Section_2_Preliminaries",
    "GeometryCycle": "Section_2_Preliminaries",
    "Gluing": "Section_2_Preliminaries",
    "SetGluing": "Section_2_Preliminaries",
    "FourVariable": "Section_3_Obstruction",
    "PaperObstruction": "Section_3_Obstruction",
    "Examples": "Section_3_Obstruction",
    "PaperExampleDetails": "Section_3_Obstruction",
    "Negative": "Section_4_Negative",
    "NegativeVertex": "Section_4_Negative",
    "NegativeSwitched": "Section_4_Negative",
    "NegativeTheorem": "Section_4_Negative",
    "PaperEvents": "Section_4_Negative",
    "Positive": "Section_5_Positive",
    "PositiveSlice": "Section_5_Positive",
    "PositiveTheorem": "Section_5_Positive",
    "Singleton": "Section_5_Positive",
    "PaperKernels": "Section_5_Positive",
    "PaperSlices": "Section_5_Positive",
    "PrivateBlocks": "Section_5_Positive",
    "SliceBridge": "Section_5_Positive",
    "Main": "Section_6_MainTheorem",
    "PaperMain": "Section_6_MainTheorem",
    "PaperConvexCombination": "Section_6_MainTheorem",
}

# (key, kind, title, decl-id, [(old file basename, decl name), ...])
# Order and grouping follow the baseline rendering; titles are paper items.
BOXES = [
    ("box0", "Definition", "Venn blocks, cycle and singleton predicates",
     "common · blockA · blockB · blockC · privateBlock · Singletons",
     [("Geometry", "common"), ("Geometry", "blockA"), ("Geometry", "blockB"),
      ("Geometry", "blockC"), ("Geometry", "IsCycle"),
      ("Geometry", "Singletons"), ("PaperGeometry", "privateBlock"),
      ("PaperGeometry", "vennBlock")]),
    ("box1", "Definition", "Hypergraph, completion edges and completion",
     "PaperHypergraph · completionEdges · completion",
     [("PaperCoordinates", "PaperHypergraph"),
      ("PaperCoordinates", "completionEdges"),
      ("PaperCoordinates", "completion")]),
    ("box2", "Definition", "Multilinear set and polytope coordinates",
     "multilinearSet · polytope",
     [("PaperCoordinates", "multilinearSet"),
      ("PaperCoordinates", "polytope")]),
    ("box3", "Lemma", "Probabilistic representation (Lemma 2.1)",
     "mem_polytope_iff_expectation",
     [("PaperCoordinates", "mem_polytope_iff_expectation")]),
    ("box4", "Lemma", "Boolean moment inversion (Lemma 2.2)",
     "mass_eq_signed_moments · exists_law_with_moments_iff",
     [("MomentInversion", "mass_eq_signed_moments"),
      ("MomentConverse", "exists_law_with_moments_iff")]),
    ("box5", "Definition", "Complete edge relaxation and local laws",
     "completeEdgeRelaxation · mem_completeEdgeRelaxation_iff_consistent",
     [("PaperHypergraph", "completeEdgeRelaxation"),
      ("PaperHypergraph", "mem_completeEdgeRelaxation_iff_consistent")]),
    ("box6", "Lemma", "Alpha-cycle definition audit",
     "isCycle_iff_alpha · core_not_subset_completed_iff · NoPrivate",
     [("DefinitionAudit", "isCycle_iff_alpha"),
      ("DefinitionAudit", "core_not_subset_completed_iff"),
      ("Triangle", "NoPrivate")]),
    ("box7", "Definition", "Switching and generalized triangles",
     "switchVector · generalizedTriangle",
     [("Relaxation", "switchVector"),
      ("Relaxation", "generalizedTriangle")]),
    ("box8", "Lemma", "Switched triangle validity (Lemma 2.3)",
     "multilinearPolytope_subset_switchedGeneralizedTriangleSet",
     [("PaperTriangles",
       "multilinearPolytope_subset_switchedGeneralizedTriangleSet")]),
    ("box9", "Definition", "Distinguished and all-cycle relaxations",
     "cycleDistinguishedRelaxation · cycleAllRelaxation · cycle_relaxation_inclusions",
     [("PaperMain", "cycleDistinguishedRelaxation"),
      ("PaperMain", "cycleAllRelaxation"),
      ("PaperMain", "cycle_relaxation_inclusions")]),
    ("box10", "Theorem", "Sharp classification (Theorem 2.4)",
     "paper_sharp_classification · cycle_all_gap_nonempty",
     [("PaperMain", "paper_sharp_classification"),
      ("PaperMain", "cycle_all_gap_nonempty")]),
    ("box11", "Proposition", "Four-variable obstruction (Proposition 3.1)",
     "parity_marginals_force_equality · fourVector_CER_gap",
     [("PaperObstruction", "parity_marginals_force_equality"),
      ("PaperObstruction", "fourVector_CER_gap")]),
    ("box12", "Proposition", "Lifted local laws (Proposition 4.1)",
     "locals_consistent · locals_not_realizable · selected_witness_gap",
     [("NegativeVertex", "locals_consistent"),
      ("NegativeVertex", "locals_not_realizable"),
      ("PaperObstruction", "selected_witness_gap")]),
    ("box13", "Lemma", "Reduced-subcycle structure (Lemma 4.2)",
     "reduced_subcycle_structure",
     [("PaperGeometry", "reduced_subcycle_structure")]),
    ("box14", "Proposition", "Witness in the all-cycle relaxation (Proposition 4.3)",
     "witness_in_allCycleRelaxation",
     [("NegativeSwitched", "witness_in_allCycleRelaxation")]),
    ("box15", "Lemma", "Private-block reduction (Lemma 5.1)",
     "singleton_private_block_reduction · restore_private_blocks",
     [("PaperGeometry", "singleton_private_block_reduction"),
      ("PrivateBlocks", "restore_private_blocks")]),
    ("box16", "Definition", "Slice moments, conditions and atoms",
     "Slice.Moments · Slice.Conditions · Slice.lower · Slice.upper · Slice.atom",
     [("PositiveSlice", "Moments"), ("PositiveSlice", "Conditions"),
      ("PositiveSlice", "lower"), ("PositiveSlice", "upper"),
      ("PositiveSlice", "atom")]),
    ("box17", "Lemma", "Slice feasibility (Lemma 5.2)",
     "interval_nonempty · each_lower_le_each_upper",
     [("PositiveSlice", "interval_nonempty"),
      ("PaperSlices", "each_lower_le_each_upper")]),
    ("box18", "Proposition", "Singleton exactness (Proposition 5.3)",
     "distinguished_exact_of_singletons · allCycle_exact_of_singletons",
     [("PositiveTheorem", "distinguished_exact_of_singletons"),
      ("PositiveTheorem", "allCycle_exact_of_singletons")]),
]

SUPPLEMENT_CSS = """
.prov{position:relative;border-left:2px solid var(--line);padding-left:1rem;margin:.6rem 0 1.2rem}
.prov-label{position:absolute;left:-1.45rem;top:.2rem;writing-mode:vertical-rl;transform:rotate(180deg);font:11px/1 system-ui,sans-serif;color:#4c78c2}
.meta-note{color:var(--muted);font-size:15px}
.citation{white-space:nowrap}
ul.refs{list-style:none;padding-left:0;font-size:15px}
ul.refs li{margin:.45rem 0;padding-left:4.6em;text-indent:-4.6em;overflow-wrap:anywhere}
.katex-display{max-width:100%;overflow-x:auto;overflow-y:hidden}
.katex-display>.katex{min-width:max-content}
.lean-box .decl-id{min-width:0;max-width:100%;white-space:normal;overflow-wrap:anywhere}
.lean-box>summary{list-style:none;cursor:pointer}
.lean-box>summary::-webkit-details-marker{display:none}
.lean-box>summary::before{content:"▸";display:inline-block;flex:0 0 auto;color:var(--muted);margin-right:.4rem}
.lean-box[open]>summary::before{content:"▾"}
.reflabel{font-weight:bold}
details.proof{margin:.4rem 0 1.1rem}
details.proof>summary{cursor:pointer;font-style:italic;display:inline;color:var(--blue)}
details.proof .qed{text-align:right;font-size:1.3em;margin:0}
.env{margin:1.1rem 0}
.env .env-label{font-weight:bold}
.authors{font-variant:small-caps;text-align:center}
.affil{color:var(--muted);font-size:15px;text-align:center}
.abstract{margin:1.2rem 0;font-size:16px}
.abstract .env-label{font-style:italic}
h2{font-size:21px;line-height:1.4;margin-top:35px}
.lean-note{margin:0 0 10px;font:13px/1.6 system-ui,sans-serif;color:#596975}
"""


def fail(msg):
    raise SystemExit("generate_html: ERROR: " + msg)


def manifest_boxes():
    if not os.path.exists(MANIFEST_JSON):
        fail("fidelity manifest not found: " + MANIFEST_JSON)
    m = json.load(open(MANIFEST_JSON))
    boxes = m["boxes"]
    if len(boxes) != 19:
        fail("expected 19 manifest boxes, found %d" % len(boxes))
    return [[s for s in b["statements"]] for b in boxes]


def find_decl(path, name):
    """Locate `name` declaration block in a Lean file.

    Returns (full_text, start_line_1based, end_line_1based). The block runs
    from the declaration's first attribute/modifier line through the end of
    its proof (or body). Proofs here all end right before the next top-level
    `/--`, `@[`, or bare declaration keyword at column 0... instead we take a
    robust approach: the block ends at the last consecutive non-blank line
    following the declaration start that is indented or blank-linked, stopping
    at the next line starting at column 0 that begins a new top-level command.
    """
    lines = open(path).read().split("\n")
    start = None
    for i, ln in enumerate(lines):
        if re.match(
                r"^(?:@\[.*?\] ?)?(?:public |private |noncomputable )?"
                r"(theorem|lemma|def|abbrev|structure|instance|example)\s+"
                + re.escape(name) + r"\b", ln):
            start = i
            break
        # namespaced member: `theorem Foo.bar` may be declared as `bar` inside
        # `namespace Foo`; also match `  theorem bar` (two-space indent).
        if re.match(
                r"^(?:@[^\n]* )? *(?:public |private |noncomputable )?"
                r"(theorem|lemma|def|abbrev|structure|instance|example)\s+"
                + re.escape(name.split(".")[-1]) + r"\b", ln):
            # accept only if the enclosing namespace matches (checked below)
            start = i
            break
    if start is None:
        fail("decl %s not found in %s" % (name, path))
    # walk back over docstring / attribute lines directly above
    while start > 0 and (
            lines[start - 1].strip().startswith("/--")
            or lines[start - 1].strip().startswith("@[")
            or lines[start - 1].strip() == ""
            or (lines[start - 1].startswith(" ")
                and not lines[start - 1].strip().startswith("--"))):
        # stop if we hit a docstring opener boundary incorrectly: only absorb
        # contiguous comment/blank/attribute lines
        prev = lines[start - 1].strip()
        if prev == "" or prev.startswith("/--") or prev.startswith("@["):
            start -= 1
        elif lines[start - 1].startswith(" ") and not prev.startswith("--"):
            # continuation of an attribute; absorb
            start -= 1
        else:
            break
        if start > 0 and lines[start].strip().startswith("-/"):
            # absorbed a docstring closer; keep absorbing its body upward
            while start > 0 and not lines[start - 1].strip().startswith("/--"):
                if lines[start - 1].strip() == "":
                    break
                start -= 1
            if start > 0 and lines[start - 1].strip().startswith("/--"):
                start -= 1
            break
    # extend to end of proof/body: consume until a blank line followed by a
    # top-level (column-0) line starting a new command or namespace closer.
    end = start
    n = len(lines)
    i = start
    while i < n:
        ln = lines[i]
        if i > start and ln.strip() == "":
            # look ahead: top-level command or `end` closes the block
            j = i + 1
            while j < n and lines[j].strip() == "":
                j += 1
            if j >= n:
                end = i
                break
            nxt = lines[j]
            if re.match(
                    r"^(theorem|lemma|def|abbrev|structure|instance|example|"
                    r"namespace|end|section|@\[|/-|/--|#|import|open|variable)",
                    nxt):
                end = i - 1
                break
        end = i
        i += 1
    # trim trailing blank lines
    while end > start and lines[end].strip() == "":
        end -= 1
    return "\n".join(lines[start:end + 1]), start + 1, end + 1


def statement_of(full):
    """Statement-only form: drop docstring, trim theorem/lemma proofs at `:= by`."""
    code = full
    # drop leading docstring block
    code = re.sub(r"\A\s*/--.*?-/\s*\n", "", code, flags=re.S)
    m = re.search(r":=\s*by\b", code)
    if m and re.match(r"\s*(?:@\[.*?\] ?)?(?:public |private |noncomputable )?"
                      r"(theorem|lemma|example)\b", code):
        return code[:m.start()].rstrip()
    return code.rstrip()


def esc(s):
    return htmlmod.escape(s, quote=False)


def build_box(key, kind, title, decl_id, entries, baseline_codes):
    parts = []
    techs = []
    for (relpath, stmt, full, lo, hi) in entries:
        href = "../Formalization/%s#L%d-L%d" % (relpath, lo, hi)
        parts.append("<pre>%s</pre>" % esc(stmt))
        parts.append(
            '<div class="srcline"><a href="%s">source</a></div>' % href)
        techs.append("<pre>%s</pre>" % esc(full))
    # variable-context note where the paper/Lean indexing differs
    note = ""
    if key == "box0":
        note = ('<p class="lean-note">Lean uses edge indices 0,1,2; these '
                "correspond to the paper's edges 1,2,3.</p>")
    _ = baseline_codes  # fidelity already enforced during extraction
    return (
        '<details class="lean-box checked"><summary>'
        '<span class="lean-kind">%s</span> '
        '<span class="lean-title">%s</span> '
        '<code class="decl-id">%s</code></summary>\n%s%s\n'
        '<details class="tech-detail"><summary>Technical details</summary>\n%s\n'
        "</details>\n</details>"
        % (esc(kind), esc(title), esc(decl_id), "".join(parts), note,
           "".join(techs)))


def extract_entry(old_file, decl, manifest_codes):
    sec = SECTION_OF_FILE[old_file]
    relpath = "%s/%s.lean" % (sec, old_file)
    path = os.path.join(FORM, relpath)
    if not os.path.exists(path):
        fail("source file missing: " + relpath)
    full, lo, hi = find_decl(path, decl)
    stmt = statement_of(full)
    # fidelity: the regenerated statement must equal its manifest entry exactly
    if stmt not in manifest_codes:
        fail("fidelity: regenerated statement for %s differs from manifest"
             % (decl,))
    # ... and occur verbatim in the source
    src_text = open(path).read()
    norm_stmt = "\n".join(l.rstrip() for l in stmt.strip().split("\n"))
    if not norm_stmt or norm_stmt not in src_text:
        fail("fidelity: statement for %s not found verbatim in %s"
             % (decl, relpath))
    return relpath, stmt, full, lo, hi


NAV = ('<nav aria-label="Paper navigation"><strong>Alpha-Cycle</strong>'
       '<a href="#title">Title &amp; abstract</a>'
       '<a href="#intro">1. Introduction</a>'
       '<a href="#ai-use">Statement on AI Use</a>'
       '<a href="#prelim">2. Preliminaries</a>'
       '<a href="#counterex">3. Four-variable obstruction</a>'
       '<a href="#negative">4. Negative direction</a>'
       '<a href="#positive">5. Positive direction</a>'
       '<a href="#main-proof">6. Proof of main theorem</a>'
       '<a href="#conclusion">7. Conclusion</a>'
       '<a href="#appendix">Appendix A. AI Chats</a>'
       '<a href="#refs">References</a></nav>')


def shell_parts():
    if not os.path.exists(SHELL_PREFIX):
        fail("vendored shell prefix not found: " + SHELL_PREFIX)
    if not os.path.exists(SHELL_SCRIPTS):
        fail("vendored shell scripts not found: " + SHELL_SCRIPTS)
    head = open(SHELL_PREFIX).read()
    # Use the local repaired stylesheet (same KaTeX version and font binaries).
    css_path = os.path.join(HERE, "assets/katex-0.16.11.offline.css")
    katex_css = open(css_path).read()
    if katex_css.count("@font-face") != 20:
        fail("offline KaTeX stylesheet must contain all 20 font-face rules")
    head += '<style id="katex-css">' + katex_css + "</style>"
    head = re.sub(r"<title>.*?</title>",
                  "<title>Tightness of the Cycle-Based Relaxation for "
                  "Completed Length-Three Alpha-Cycles — formalized edition"
                  "</title>", head, flags=re.S)
    head += "<style>" + SUPPLEMENT_CSS + "\n</style></head>"
    tail_bits = re.findall(
        r"<script\b[^>]*>.*?</script>",
        open(SHELL_SCRIPTS).read(), re.S)
    if len(tail_bits) < 3:
        fail("expected KaTeX, auto-render and math initializer scripts in shell assets")
    if not any("renderMathInElement(document.body" in b for b in tail_bits):
        fail("shell assets are missing the equation-rendering initializer")
    tail = "".join(tail_bits)
    tail += "</body></html>"
    return head, tail


def assemble():
    json.load(open(os.path.join(HERE, "verification.json")))
    codes = manifest_boxes()
    if len(codes) != len(BOXES):
        fail("baseline/box manifest length mismatch")
    entries_html = {}
    for idx, (key, kind, title, decl_id, decls) in enumerate(BOXES):
        parts = []
        for (old_file, decl) in decls:
            parts.append(extract_entry(old_file, decl, codes[idx]))
        entries_html[key] = build_box(key, kind, title, decl_id, parts,
                                      codes[idx])
    tpl = open(os.path.join(HERE, "prose_template.html")).read()
    for key, box_html in entries_html.items():
        ph = "<!--BOX:%s-->" % key
        if ph not in tpl:
            fail("placeholder missing in template: " + ph)
        tpl = tpl.replace(ph, box_html)
    if "<!--BOX:" in tpl:
        fail("unfilled box placeholders remain")
    affil = (
        '<p class="affil">PDF: <a target="_blank" rel="noopener" '
        'href="alpha_cycle.pdf">Papers/alpha_cycle.pdf</a>. Lean library: '
        '<a target="_blank" rel="noopener" href="../Formalization/AlphaCycle.lean">'
        "Formalization/</a> (root module <code>AlphaCycle.lean</code>; "
        "BibTeX: <a target=\"_blank\" rel=\"noopener\" "
        'href="citation.bib">citation.bib</a>).</p>')
    if "<!--AFFIL-->" not in tpl:
        fail("affil placeholder missing in template")
    tpl = tpl.replace("<!--AFFIL-->", affil)
    tpl = re.sub(
        r'<p class="authors">.*?</p>',
        '<p class="authors">Aykut Arslan<sup>*</sup> and Meta AI</p>', tpl,
        count=1, flags=re.S)
    tpl = re.sub(
        r'<p class="authors reviewer">.*?</p>',
        '<p class="authors reviewer">Reviewed by Kien Le<sup>&dagger;</sup></p>',
        tpl, count=1, flags=re.S)
    raudit = '<h2 id="refs">'
    if raudit not in tpl:
        fail("references anchor missing in template")
    head, tail = shell_parts()
    return (head + "<body>" + NAV + "<main>" + tpl + "</main>" + tail)


def main():
    check = len(sys.argv) > 1 and sys.argv[1] == "--check"
    out = os.path.join(HERE, "alpha_cycle_interactive.html")
    html = assemble()
    if check:
        if not os.path.exists(out):
            fail("no checked-in HTML to compare against")
        cur = open(out).read()
        if cur != html:
            fail("--check: checked-in HTML differs from regenerated output; "
                 "run generate_html.py to refresh")
        print("generate_html --check: OK")
    else:
        open(out, "w").write(html)
        print("wrote %s (%d bytes)" % (out, len(html)))


if __name__ == "__main__":
    main()