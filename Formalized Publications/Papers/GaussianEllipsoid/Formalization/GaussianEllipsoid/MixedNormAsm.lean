/-
MixedNormBound assembly candidate (MNASM).

Target: `MixedNormBody` / `MixedNormBound` in
`GaussianEllipsoid/BelowObjects.lean` (used verbatim; nothing weakened).
This file proves the assembly spine: parameter positivity (C1-C3), the
body combiner, per-point branch and per-`d` three-event conditionals
(instantiable forms of `MBMulti.mixed_branch_combine` and
`MBMulti.good_event_measure_bound`), and the end-to-end conditional
`mixedNormBound_of_inputs` carrying the missing C4/C5 pieces as explicit
hypotheses `hProb` / `hPoint`, plus the uniform lift to `MixedNormBound`.
-/
import GaussianEllipsoid.BelowObjects

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory
open scoped BigOperators

/-- C1-C3: concrete parameter witness `η = 1/2`, `c = 1`. -/
theorem mnasM_param_witness : ∃ η c : ℝ, 0 < η ∧ η < 1 ∧ 0 < c :=
  ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩

/-- Assembly spine: the five conjuncts give `MixedNormBody` definitionally. -/
theorem mnasM_body_of_parts {n : ℕ → ℕ} {δ η c : ℝ}
    {G : Π d, Set (Sample d (n d))}
    (hη0 : 0 < η) (hη1 : η < 1) (hc : 0 < c)
    (hProb : Filter.limsup
      (fun d => ((gaussianSampleLaw d (n d)) (G d)ᶜ).toReal)
      Filter.atTop ≤ δ)
    (hPoint : ∀ d, ∀ x ∈ G d, ∀ y : Vector (n d), (∑ i, y i) = 0 →
      c * mixedNorm η d (n d) y ≤ nuclearNorm (centeredAdjoint x y)) :
    MixedNormBody n δ η c G :=
  ⟨hη0, hη1, hc, hProb, hPoint⟩

/-- C5 at one point from the branch disjunction plus the cap bound
(M-C5a/M-C5b shape; cf. `MBMulti.mixed_branch_combine`). -/
theorem mnasM_pointwise_of_branches {cA N Bplus Bhead Btail Hlo Thi : ℝ}
    (hTri : Bhead - Btail ≤ Bplus)
    (hEither : cA * N ≤ Bplus ∨
      (Hlo ≤ Bhead ∧ Btail ≤ Thi ∧ Thi ≤ Hlo / 2))
    (hCap : cA * N ≤ Hlo / 2) :
    cA * N ≤ Bplus := by
  rcases hEither with h | ⟨hH, hT, hP⟩
  · exact h
  · linarith

/-- Instantiation of the branch lemma to `c * mixedNorm ≤ nuclearNorm`. -/
theorem mnasM_pointwise_inst_of_branches {d n : ℕ} {η c : ℝ}
    {x : Sample d n} {y : Vector n}
    {Bhead Btail Hlo Thi : ℝ}
    (hTri : Bhead - Btail ≤ nuclearNorm (centeredAdjoint x y))
    (hEither : c * mixedNorm η d n y ≤ nuclearNorm (centeredAdjoint x y) ∨
      (Hlo ≤ Bhead ∧ Btail ≤ Thi ∧ Thi ≤ Hlo / 2))
    (hCap : c * mixedNorm η d n y ≤ Hlo / 2) :
    c * mixedNorm η d n y ≤ nuclearNorm (centeredAdjoint x y) :=
  mnasM_pointwise_of_branches hTri hEither hCap

/-- Per-`d` good-event bound from the three-event inclusion plus per-event
bounds (M-C4a shape; cf. `MBMulti.good_event_measure_bound`). -/
theorem mnasM_compl_le_of_three {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {G E1 E2 E3 : Set Ω} {p1 p2 p3 : ENNReal}
    (hSub : Gᶜ ⊆ E1 ∪ (E2 ∪ E3))
    (h1 : μ E1 ≤ p1) (h2 : μ E2 ≤ p2) (h3 : μ E3 ≤ p3) :
    μ Gᶜ ≤ p1 + (p2 + p3) := by
  have a : μ (E1 ∪ (E2 ∪ E3)) ≤ μ E1 + μ (E2 ∪ E3) :=
    measure_union_le _ _
  have b : μ (E2 ∪ E3) ≤ μ E2 + μ E3 := measure_union_le _ _
  have c : μ (E1 ∪ (E2 ∪ E3)) ≤ μ E1 + (μ E2 + μ E3) :=
    a.trans (add_le_add le_rfl b)
  have d : μ E1 + (μ E2 + μ E3) ≤ p1 + (p2 + p3) :=
    add_le_add h1 (add_le_add h2 h3)
  exact (measure_mono hSub).trans (c.trans d)

/-- End-to-end conditional assembly: for concrete `n` and `δ`, the missing
C4/C5 pieces as explicit hypotheses yield the `MixedNormBody` witness. -/
theorem mixedNormBound_of_inputs
    (n : ℕ → ℕ) (_hn : ∀ d, 0 < n d)
    (_hr : Filter.limsup (dimensionRatio n) Filter.atTop < (1 / 4 : ENNReal))
    (δ : ℝ) (_hδ : 0 < δ)
    (η c : ℝ) (G : Π d, Set (Sample d (n d)))
    (hη0 : 0 < η) (hη1 : η < 1) (hc : 0 < c)
    (hProb : Filter.limsup
      (fun d => ((gaussianSampleLaw d (n d)) (G d)ᶜ).toReal)
      Filter.atTop ≤ δ)
    (hPoint : ∀ d, ∀ x ∈ G d, ∀ y : Vector (n d), (∑ i, y i) = 0 →
      c * mixedNorm η d (n d) y ≤ nuclearNorm (centeredAdjoint x y)) :
    ∃ η' c' : ℝ, ∃ G' : Π d, Set (Sample d (n d)),
      MixedNormBody n δ η' c' G' :=
  ⟨η, c, G, hη0, hη1, hc, hProb, hPoint⟩

/-- Uniform lift: uniform hard-input providers give `MixedNormBound`. -/
theorem mixedNormBound_of_uniform_inputs
    (hHard : ∀ (n : ℕ → ℕ), (∀ d, 0 < n d) →
      Filter.limsup (dimensionRatio n) Filter.atTop < (1 / 4 : ENNReal) →
      ∀ δ : ℝ, 0 < δ →
        ∃ η c : ℝ, ∃ G : Π d, Set (Sample d (n d)),
          MixedNormBody n δ η c G) :
    MixedNormBound := by
  intro n hn hr δ hδ
  exact hHard n hn hr δ hδ

#print axioms mnasM_param_witness
#print axioms mnasM_body_of_parts
#print axioms mnasM_pointwise_of_branches
#print axioms mnasM_pointwise_inst_of_branches
#print axioms mnasM_compl_le_of_three
#print axioms mixedNormBound_of_inputs
#print axioms mixedNormBound_of_uniform_inputs

end GaussianEllipsoid
