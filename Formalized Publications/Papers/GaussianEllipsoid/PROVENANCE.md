# Provenance

Small receipts for this reformat. Full historical evidence stays in the
source project (`projects/arslan/agents/gaussian-ellipsoid/`) and in git
history; nothing below re-audits the mathematics.

## Base

- New branch `arslan/gaussian-ellipsoid-atlas-format` from cached
  `origin/main` `ad6e2c0eea33f0fa3f7812a130a769c6f8d731cc` (Oct 28; remote
  refresh unavailable, used as-is). No Hypercube/Alpha branch content.
- Worktree
  `/Users/aykutarslan/projects/Hypercube_Inequality_Formalization/kep-gaussian-atlas-wt`
  (session-created, isolated). Existing checkouts untouched.

## Authoritative inputs (exact bytes)

- Manuscript: `gaussian_ellipsoid (new format).tex`, 162136 bytes,
  sha256 `2b8bec7571de45ef59b076c81f4455b7becce5d6d726f2266efdfd9e34135e37`.
  Checked in as `Papers/Latex/main.tex` (byte-identical).
- PDF: `paper.pdf`, 685018 bytes, 62 pages,
  sha256 `24dbb073079ead0fec59a1a93bc695b6b2818cd9cf1f37dfec23ef6a36264181`.
  Checked in as `Papers/gaussian_ellipsoid.pdf` (byte-identical).
- Support files (`stylelibrary.tex`, `flexart.sty`, `ulem.sty`,
  `bib.bib` == `refs.bib`, `readme-library.tex`, `settings.tex`,
  `BUILD_PDF.md`, KaTeX JS): exact copies from
  `arslan_gaussian_ellipsoid_for_kep_stem_math.zip`
  (`projects/arslan/docs/gaussian-ellipsoid/`); see `Papers/assets/README.md`
  for the KaTeX byte provenance.
- Frozen Lean sources: 770 modules under
  `projects/arslan/agents/gaussian-ellipsoid/`
  (`GaussianEllipsoid/` 47 + `GaussianEllipsoidNative/` 723),
  pin Lean `v4.34.0-rc2` + mathlib
  `85e3a25e006c35636f0e53b0e9296caca2685bc0`, `autoImplicit = false`.
  Copied byte-for-byte to `Formalization/` (verified by
  `Formalization/check_preservation.py`).
- Coverage provenance: `GaussianEllipsoid_FINAL_Coverage.json`
  (40 named statements + 8 supplemental AHH assertions, 1178 mapping
  checks, 235 endpoint axiom checks, 10980-declaration transitive sweep
  with only standard axioms) and `coverage.csv` remain the historical
  receipts in `agents/gaussian-ellipsoid/`; they are not fresh checks.
  `LEAN_SOURCES_SHA256SUMS.txt` keys the 723 backend files by bare
  filename (and names files absent from the current tree), so it is
  kept as provenance only, not as the preservation gate.

## What changed (formatting only)

- Moved the proof package `agents/gaussian-ellipsoid/` → canonical
  `src/gaussian-ellipsoid/` (this package), leaving a forwarding README
  at the old location. No `.lean` byte changed; only the package prefix
  is new. The pre-move originals were then removed from this worktree
  (771 deletions: 770 modules + the draft 8MB HTML); small receipts and
  pins stay under `agents/gaussian-ellipsoid/`, full history in git.
  New files: `Formalization/GaussianEllipsoid.lean` (root),
  `Formalization/SOURCES_SHA256.txt` (frozen 770-hash ledger),
  `Section_*/README.md`, `FILE_MAP.md`, the two `Formalization/*.py`
  check scripts, `Papers/` generator + template + inventory + tests,
  `Comparator/` audit + inventory, `Readme.md`, `citation.bib`,
  `LICENSE`, this file.
- Preservation after the move is ledger-based
  (`Formalization/check_preservation.py` checks every module against
  `SOURCES_SHA256.txt`, plus the pre-move originals wherever present).
- Headers in some moved files still carry old `UNPROVED` descriptions
  from before the final assembly; the proofs live in the later final
  modules (e.g. `StrictThresholdProjectFinal.lean`). Do not infer
  mathematical gaps from historical headers.
- No version port: the Atlas default Lean `v4.35.0` is not used here.

## Verification record

- `Formalization/check_preservation.py`: 770 modules byte-identical,
  import closure over 771 nodes in 43 levels, no
  `sorry`/`admit`/`native_decide`/`axiom`/`unsafe` in code.
- `Papers/generate_html.py --check`: deterministic; all 167 inventory
  declarations resolve verbatim in `Formalization/` with valid
  `file#Lx-Ly` source links (48 boxes).
- `Papers/test_html_rendering.py`: static profile 2109 equations,
  48 boxes, 167 source links, 20 font faces, no external assets, no
  audit phrases, no proof bodies in main blocks.
- Lean rebuild + browser render: see `Papers/verification.json`.
