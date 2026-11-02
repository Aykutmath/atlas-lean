# Embedded KaTeX assets

`katex-0.16.11.offline.css` supplies the 20 font faces used by the
embedded KaTeX 0.16.11 renderer (fonts embedded as data URIs; no font
files needed). `katex.min.js` and `auto-render.min.js` are the KaTeX
0.16.11 renderer and auto-renderer. The generator inlines all three
into the HTML; readers need only the HTML file, not this assets folder
or a CDN connection.

Provenance: `katex.min.js` (md5 `f4e1ebdc2d32cfb3d40663302c96c4ff`) and
`auto-render.min.js` (md5 `71052e38485a2b06c4de2928b885aab9`) are
byte-identical to the files shipped in the supplied manuscript package
(`arslan_gaussian_ellipsoid_for_kep_stem_math.zip`,
`projects/arslan/docs/gaussian-ellipsoid/assets/katex/`) and to the
scripts embedded in the Alpha Cycle reference rendering. The offline
stylesheet is the repaired KaTeX 0.16.11 stylesheet shared with the
Alpha Cycle package (20 `@font-face` rules; the generator fails unless
all 20 are present). No mathematical statements or Lean sources were
changed.

KaTeX project: https://github.com/KaTeX/KaTeX (MIT license).
