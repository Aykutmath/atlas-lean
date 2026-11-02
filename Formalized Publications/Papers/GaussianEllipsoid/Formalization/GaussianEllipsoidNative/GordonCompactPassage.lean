import GordonCompactAnalysis

noncomputable section
open MeasureTheory Filter Topology
namespace BMGordonCompact

def compactMinMax {K L Ω : Type*} (X : K × L → Ω → ℝ) (ω : Ω) : ℝ :=
  sInf ((fun k => sSup ((fun l => X (k,l) ω) '' Set.univ)) '' Set.univ)

/-- Pure compact passage, reused from the supplied GordonCompact proof.
There is no Gaussianity or centeredness requirement here: an actual proved
finite comparison can be supplied for the shared-drift processes. -/
theorem compact_comparison_of_finite
    (K L : Type) [MetricSpace K] [MetricSpace L]
    [CompactSpace K] [CompactSpace L] [Nonempty K] [Nonempty L]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : K × L → Ω → ℝ)
    (hContX : ∀ᵐ ω ∂P, Continuous fun p : K × L => X p ω)
    (hContY : ∀ᵐ ω ∂P, Continuous fun p : K × L => Y p ω)
    (hFinite : ∀ (tK : Finset K) (tL : Finset L),
      ∀ (_ : tK.Nonempty) (_ : tL.Nonempty),
      ∀ [Fintype ↥tK] [Fintype ↥tL],
      ∀ [_iK : Nonempty ↥tK] [_iL : Nonempty ↥tL],
      (∫ ω, finMin (fun i : ↥tK => finMax (fun j : ↥tL => X (i.1,j.1) ω)) ∂P) ≤
      ∫ ω, finMin (fun i : ↥tK => finMax (fun j : ↥tL => Y (i.1,j.1) ω)) ∂P)
    (hNetInt : ∀ (tK : Finset K) (tL : Finset L),
      ∀ (_ : tK.Nonempty) (_ : tL.Nonempty),
      ∀ [Fintype ↥tK] [Fintype ↥tL],
      ∀ [_iK : Nonempty ↥tK] [_iL : Nonempty ↥tL],
      Integrable
        (fun ω => finMin (fun i : ↥tK => finMax (fun j : ↥tL => X (i.1,j.1) ω))) P ∧
      Integrable
        (fun ω => finMin (fun i : ↥tK => finMax (fun j : ↥tL => Y (i.1,j.1) ω))) P)
    (hDom : ∃ gX gY : Ω → ℝ, Integrable gX P ∧ Integrable gY P ∧
      ∀ (tK : Finset K) (tL : Finset L),
      ∀ (_ : tK.Nonempty) (_ : tL.Nonempty),
      ∀ [Fintype ↥tK] [Fintype ↥tL],
      ∀ [_iK : Nonempty ↥tK] [_iL : Nonempty ↥tL],
      (∀ᵐ ω ∂P,
        ‖finMin (fun i : ↥tK => finMax (fun j : ↥tL => X (i.1,j.1) ω))‖ ≤ gX ω) ∧
      (∀ᵐ ω ∂P,
        ‖finMin (fun i : ↥tK => finMax (fun j : ↥tL => Y (i.1,j.1) ω))‖ ≤ gY ω)) :
    (∫ ω, compactMinMax X ω ∂P) ≤ ∫ ω, compactMinMax Y ω ∂P := by
  choose tK htKne htKcov using fun m => exists_finset_net K m
  choose tL htLne htLcov using fun m => exists_finset_net L m
  haveI hFK : ∀ m, Fintype ↥(tK m) := fun m => inferInstance
  haveI hFL : ∀ m, Fintype ↥(tL m) := fun m => inferInstance
  haveI hNK : ∀ m, Nonempty ↥(tK m) :=
    fun m => ⟨⟨(htKne m).choose, (htKne m).choose_spec⟩⟩
  haveI hNL : ∀ m, Nonempty ↥(tL m) :=
    fun m => ⟨⟨(htLne m).choose, (htLne m).choose_spec⟩⟩
  have hcovK : ∀ m, ∀ x : K, ∃ i : ↥(tK m), dist i.1 x ≤ 1 / ((m : ℝ) + 1) := by
    intro m x
    obtain ⟨c, hc, hdist⟩ := htKcov m x
    exact ⟨⟨c, hc⟩, le_of_lt hdist⟩
  have hcovL : ∀ m, ∀ x : L, ∃ j : ↥(tL m), dist j.1 x ≤ 1 / ((m : ℝ) + 1) := by
    intro m x
    obtain ⟨c, hc, hdist⟩ := htLcov m x
    exact ⟨⟨c, hc⟩, le_of_lt hdist⟩
  have hstep : ∀ m : ℕ,
      ∫ ω, finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => X (i.1, j.1) ω)) ∂P ≤
      ∫ ω, finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => Y (i.1, j.1) ω)) ∂P := by
    intro m
    exact hFinite (tK m) (tL m) (htKne m) (htLne m)
  have haeX : ∀ᵐ ω ∂P,
      Tendsto (fun m => finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => X (i.1, j.1) ω)))
        atTop (𝓝 (compactMinMax X ω)) :=
    hContX.mono fun ω hω =>
      netMinMax_tendsto_sInf_sSup (fun p => X p ω)
        (fun m => ↥(tK m)) (fun m => ↥(tL m))
        (fun m i => i.1) (fun m j => j.1) hcovK hcovL hω
  have haeY : ∀ᵐ ω ∂P,
      Tendsto (fun m => finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => Y (i.1, j.1) ω)))
        atTop (𝓝 (compactMinMax Y ω)) :=
    hContY.mono fun ω hω =>
      netMinMax_tendsto_sInf_sSup (fun p => Y p ω)
        (fun m => ↥(tK m)) (fun m => ↥(tL m))
        (fun m i => i.1) (fun m j => j.1) hcovK hcovL hω
  obtain ⟨gX, gY, hgXint, hgYint, hdom⟩ := hDom
  have hmeasX : ∀ m,
      AEStronglyMeasurable (fun ω => finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => X (i.1, j.1) ω))) P := by
    intro m
    exact ((hNetInt (tK m) (tL m) (htKne m) (htLne m)).1).aestronglyMeasurable
  have hmeasY : ∀ m,
      AEStronglyMeasurable (fun ω => finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => Y (i.1, j.1) ω))) P := by
    intro m
    exact ((hNetInt (tK m) (tL m) (htKne m) (htLne m)).2).aestronglyMeasurable
  have hdomX : ∀ m, ∀ᵐ ω ∂P,
      ‖finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => X (i.1, j.1) ω))‖ ≤ gX ω := by
    intro m
    exact ((hdom (tK m) (tL m) (htKne m) (htLne m)).1)
  have hdomY : ∀ m, ∀ᵐ ω ∂P,
      ‖finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => Y (i.1, j.1) ω))‖ ≤ gY ω := by
    intro m
    exact ((hdom (tK m) (tL m) (htKne m) (htLne m)).2)
  have hlimX : Tendsto
      (fun m => ∫ ω, finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => X (i.1, j.1) ω)) ∂P)
      atTop (𝓝 (∫ ω, compactMinMax X ω ∂P)) :=
    integral_tendsto_of_dominated P hgXint hmeasX hdomX haeX
  have hlimY : Tendsto
      (fun m => ∫ ω, finMin (fun i : ↥(tK m) =>
        finMax (fun j : ↥(tL m) => Y (i.1, j.1) ω)) ∂P)
      atTop (𝓝 (∫ ω, compactMinMax Y ω ∂P)) :=
    integral_tendsto_of_dominated P hgYint hmeasY hdomY haeY
  first
    | exact le_of_tendsto_of_tendsto hlimX hlimY
        (Filter.Eventually.of_forall hstep)
    | exact le_of_tendsto_of_tendsto hlimX hlimY hstep
    | exact le_of_tendsto_of_tendsto hlimX
        (Filter.Eventually.of_forall hstep) hlimY
    | exact le_of_tendsto_of_tendsto hlimX hstep hlimY


#print axioms compact_comparison_of_finite
end BMGordonCompact
