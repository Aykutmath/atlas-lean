/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aykut Arslan

Independent challenge for the Alpha-Cycle main theorem (Paper Theorem 2.4,
`AlphaCycle.PaperHypergraph.paper_sharp_classification`).

The paper-facing definitions are stated independently in the `Challenge/`
modules below, by design: they import only Mathlib and each other, never
the solution (`Formalization/`), so changing a solution definition cannot
change both sides of the comparison. They duplicate the paper-facing
solution definitions under the same names and with the same bodies
(byte-identical source excerpts, elaborated file-by-file in dependency
order exactly like the solution build); `definition_names` in the JSON
config is deliberately empty, so all of them are compared by full
structural body equality, recursively, rather than as signature-only
holes. The theorem is the paper-facing classification (both relaxations
equal the completed polytope if and only if each pair-only block is a
singleton), stated with these challenge definitions; its proof here is the
single authorized `sorry`. The comparator checks that the solution proves
the same statement with only the permitted axioms.

`sorry` is authorized in the challenge excerpt holding the main theorem
only. The solution (`Formalization/`) contains no `sorry`, `admit`,
`native_decide`, or custom axioms.
-/
import Challenge.Section_6_MainTheorem.PaperMain
