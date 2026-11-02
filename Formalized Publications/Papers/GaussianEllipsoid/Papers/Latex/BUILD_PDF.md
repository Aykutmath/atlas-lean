# PDF reproduction and visual review

The supplied main LaTeX source is preserved byte-for-byte as `paper.tex`.
The two attachment filenames were mapped to the names it imports:
`flexart(1).sty` to `flexart.sty`, and `stylelibrary (1).tex` to `stylelibrary.tex`.
No mathematical or typographic source edits were made.

Build from this directory with a standard TeX Live installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

`ulem.sty` is required by the supplied style library. The execution environment
lacked that standard package, so the unmodified CTAN version dated 2019-11-18
was downloaded from CTAN and is included as `ulem.sty` with its original
copyright and redistribution notice. Its SHA256 is
`c97c15736b46cf13071c52070c07aa933fc8253748422d0df56e97286b563685`.
This supplied dependency is not an edit to the manuscript.

CTAN source used:
https://mirror.math.princeton.edu/pub/CTAN/macros/latex/contrib/ulem/ulem.sty

The successful build produced 62 pages (685018 bytes). The final LaTeX log
contained no undefined references, missing citations, overfull boxes or
underfull boxes. Its only warning was that microtype could not apply its
footnote patch. All 62 pages were rasterized and checked in contact sheets;
the first page was also inspected at a larger size. No visible clipping,
blank body pages, overlapping text or missing mathematical glyphs were found
in those inspections. This is a layout check, not a mathematical review.

`compiled-paper.bbl` and `paper-labels.json` record the bibliography and
numbering used by the HTML generator. `bib.bbl` is the original supplied
bibliography output; `bib.bib` and `refs.bib` are identical copies of the
supplied bibliography source.
