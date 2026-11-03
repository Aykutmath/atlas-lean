/-
# AlphaCycle formalization — library root

Atlas-style layout: `Formalization/` is the Lake source root and this file
imports every section module in paper order (Sections 1–6).
Paper correspondence and build instructions: see `../Readme.md`; the
interactive paper rendering is `../Papers/alpha_cycle_interactive.html`.

Namespaces inside the section files are unchanged (`AlphaCycle`,
`AlphaCycle.PaperHypergraph`, …), so fully-qualified theorem names are
exactly as checked; only the module import paths reflect the new layout.

Known cross-section edge (documented, Lake-checked): the Section 3 example
files (`Section_3_Obstruction.Examples`, `Section_3_Obstruction.PaperObstruction`,
`Section_3_Obstruction.PaperExampleDetails`) build on the Section 6 endpoints
to exhibit the gap; see `Section_3_Obstruction/README.md`.
-/

-- Section 1 — Introduction (Venn blocks, cycle and singleton predicates)
import Section_1_Introduction.Geometry

-- Section 2 — Preliminaries (laws, moments, CER, completion, switching)
import Section_2_Preliminaries.FiniteLaw
import Section_2_Preliminaries.Basic
import Section_2_Preliminaries.Core
import Section_2_Preliminaries.MomentInversion
import Section_2_Preliminaries.MomentConverse
import Section_2_Preliminaries.PaperInversionIdentities
import Section_2_Preliminaries.PaperTranscription
import Section_2_Preliminaries.Polytope
import Section_2_Preliminaries.Triangle
import Section_2_Preliminaries.Relaxation
import Section_2_Preliminaries.AllCycles
import Section_2_Preliminaries.CyclePermutation
import Section_2_Preliminaries.LocalVector
import Section_2_Preliminaries.PaperCoordinates
import Section_2_Preliminaries.PaperHypergraph
import Section_2_Preliminaries.PaperGeometry
import Section_2_Preliminaries.PaperCycleCorrespondence
import Section_2_Preliminaries.PaperTriangles
import Section_2_Preliminaries.DefinitionAudit
import Section_2_Preliminaries.Reindex
import Section_2_Preliminaries.GeometryCycle
import Section_2_Preliminaries.Gluing
import Section_2_Preliminaries.SetGluing

-- Section 3 — The four-variable obstruction
import Section_3_Obstruction.FourVariable
import Section_3_Obstruction.Examples
import Section_3_Obstruction.PaperObstruction
import Section_3_Obstruction.PaperExampleDetails

-- Section 4 — Negative direction: lifting the obstruction
import Section_4_Negative.Negative
import Section_4_Negative.NegativeVertex
import Section_4_Negative.NegativeSwitched
import Section_4_Negative.NegativeTheorem
import Section_4_Negative.PaperEvents

-- Section 5 — Positive direction: the singleton case
import Section_5_Positive.PositiveSlice
import Section_5_Positive.Positive
import Section_5_Positive.Singleton
import Section_5_Positive.PaperKernels
import Section_5_Positive.PaperSlices
import Section_5_Positive.PrivateBlocks
import Section_5_Positive.SliceBridge
import Section_5_Positive.PositiveTheorem

-- Section 6 — Proof of the main theorem
import Section_6_MainTheorem.Main
import Section_6_MainTheorem.PaperConvexCombination
import Section_6_MainTheorem.PaperMain
