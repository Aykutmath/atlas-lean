# Embedded KaTeX stylesheet

`katex-0.16.11.offline.css` supplies the 20 font faces used by the embedded
KaTeX 0.16.11 renderer. The generator inlines this stylesheet into the HTML;
readers need only the HTML file, not this assets folder or a CDN connection.

The font binaries are unchanged from the supplied Hypercube style reference
(`handoff/style-reference/hypercube_formalization.html`). The old shell donor's
font embedding had collapsed the CSS rule boundaries and family descriptors.
Those boundaries and descriptors were recovered from the reference; the
KaTeX 0.16.11 layout rules and base font rule were retained. No mathematical
statements or Lean sources were changed.

KaTeX project: https://github.com/KaTeX/KaTeX (MIT license).

## Vendored document shell

`shell_prefix.html` is the document head (doctype, meta, title, donor
stylesheet) and `shell_scripts.html` holds the three trailing scripts (KaTeX
library, auto-render library, equation-rendering initializer). Both are
byte-identical excerpts of the Nov-1 verified
`Papers/alpha_cycle_interactive.html`, vendored so the paper regenerates
from this public folder alone: `generate_html.py` inlines them together with
the stylesheet above, and no sibling-package HTML or private rendering is
read. `lean_boxes_manifest.json` (next to `generate_html.py`) is the
committed Lean-box fidelity baseline derived from the same verified edition.

Regression check: `python3 Papers/test_html_rendering.py --browser` from the
Alpha Cycle package root. This requires Playwright and Chromium on the test
machine and checks all rendered equations and embedded font faces offline.
