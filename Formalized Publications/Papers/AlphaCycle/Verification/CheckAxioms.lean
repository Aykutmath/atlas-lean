import AlphaCycle

/-! This command file inspects already kernel-checked declarations. It does not
construct proofs or use evaluation to establish any mathematical proposition. -/
#print axioms AlphaCycle.sharp_classification
#print axioms AlphaCycle.allCycle_gap_nonempty
#print axioms AlphaCycle.FourVariable.obstruction
#print axioms AlphaCycle.NegativeVertex.witness_in_allCycleRelaxation
#print axioms AlphaCycle.Geometry.isCycle_iff_alpha
#print axioms AlphaCycle.SupportedCycle.two_le_card
#print axioms AlphaCycle.PaperHypergraph.paper_sharp_classification
#print axioms AlphaCycle.mem_completeEdgeRelaxation_iff_cell_inequalities
#print axioms AlphaCycle.Geometry.private_block_reduction
#print axioms AlphaCycle.Law.restorePrivateWithKernels_marginals
#print axioms AlphaCycle.Slice.atom_reconstruction
#print axioms AlphaCycle.PaperTranscription.malformed_singleton_not_normalized

open Lean in
/-- Project modules in the Atlas layout: the root plus one per paper section.
Only the module paths changed in the move; namespaces (hence theorem names)
are unchanged. -/
def isProjectModule (modName : Name) : Bool :=
  (`AlphaCycle).isPrefixOf modName ||
  (`Section_1_Introduction).isPrefixOf modName ||
  (`Section_2_Preliminaries).isPrefixOf modName ||
  (`Section_3_Obstruction).isPrefixOf modName ||
  (`Section_4_Negative).isPrefixOf modName ||
  (`Section_5_Positive).isPrefixOf modName ||
  (`Section_6_MainTheorem).isPrefixOf modName

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.allImportedModuleNames[idx.toNat]!
      if isProjectModule modName then
        if !modules.contains modName then modules := modules.push modName
        if info.isAxiom then
          throwError "Project-defined axiom: {name}"
        if info.isUnsafe then
          throwError "Unsafe project declaration: {name}"
        let deps ← collectAxioms name
        for dep in deps do
          unless #[`propext, `Classical.choice, `Quot.sound].contains dep do
            throwError "Unapproved axiom {dep} in {name}"
        logInfo m!"AUDITED {name}: {deps}"
        count := count + 1
  unless count > 0 do throwError "No project declarations were audited"
  logInfo m!"AXIOM AUDIT PASSED: {count} declarations in {modules.size} project modules; only propext, Classical.choice, Quot.sound."
