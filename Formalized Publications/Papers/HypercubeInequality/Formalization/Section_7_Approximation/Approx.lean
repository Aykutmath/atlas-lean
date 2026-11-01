module

/-
# Approximation by finite laws (HI-ZERO, HI-INFGAP, HI-FINMOM, ...)

Paper Section 7: endpoint cases (zero/infinite gaps), finite moments from
finite gaps, and (in progress) quantization plus determinant-monomial
convergence toward the general Borel main theorem.
-/

public import Mathlib
public import Section_1_Introduction.Core
public import Section_6_OneStep.Onestep
public import Section_11_Sharpness.Sharp
public import Section_8_MainTheorem.Induction

namespace HypercubeInequality

open MeasureTheory Measure Finset Filter
open scoped ENNReal NNReal BigOperators Nat Topology

section MarginalGap

variable {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d))) (j : Fin d)

/-- Coordinate marginal on the real line. -/
@[expose] public noncomputable def coordMarginal : Measure ℝ :=
  Measure.map (fun x : EuclideanSpace ℝ (Fin d) => x j) ν

/-- Marginals of probability laws are probability laws. -/
public instance coordMarginal_prob [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (coordMarginal ν j) := ⟨by
  simp only [coordMarginal, Measure.map_apply (measurable_coord j)
    MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩

public theorem measurable_gapReal :
    Measurable (fun q : ℝ × ℝ => (‖q.1 - q.2‖₊ : ℝ≥0∞)) :=
  measurable_coe_nnreal_ennreal.comp
    (measurable_fst.sub measurable_snd).nnnorm

/-- Gaps push forward to the real line. -/
public theorem gap_eq_marginal_gap [SFinite ν] :
    gap j ν = ∫⁻ q : ℝ × ℝ, (‖q.1 - q.2‖₊ : ℝ≥0∞)
      ∂((coordMarginal ν j).prod (coordMarginal ν j)) := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) :=
    measurable_coord j
  have hmap := Measure.map_prod_map ν ν hmeas hmeas
  have hme : Measurable (Prod.map (fun x : EuclideanSpace ℝ (Fin d) => x j)
      (fun x : EuclideanSpace ℝ (Fin d) => x j)) :=
    hmeas.prodMap hmeas
  simp only [gap, coordMarginal]
  rw [hmap, lintegral_map measurable_gapReal hme]
  apply lintegral_congr_ae
  filter_upwards with p
  rfl

end MarginalGap

section InfGap

variable {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))

/-- A finite product with a top factor and no zeros is top. -/
public theorem prod_eq_top_aux {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ≥0∞)
    (j : ι) (hj : j ∈ s) (hinf : f j = ∞) (h0 : ∀ i ∈ s, f i ≠ 0) :
    ∏ i ∈ s, f i = ∞ := by
  revert hj h0
  induction s using Finset.induction with
  | empty =>
    intro hj h0
    simp at hj
  | @insert a s hna ih =>
    intro hj h0
    rw [Finset.prod_insert hna]
    by_cases haj : a = j
    · subst haj
      rw [hinf]
      exact ENNReal.top_mul (Finset.prod_ne_zero_iff.mpr
        (fun i hi => h0 i (Finset.mem_insert_of_mem hi)))
    · have hj' : j ∈ s := by
        rcases Finset.mem_insert.mp hj with h | h
        · exact absurd h.symm haj
        · exact h
      have ih' := ih hj' (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      rw [ih']
      exact ENNReal.mul_top (h0 a (Finset.mem_insert_self a s))

/-- HI-INFGAP: an infinite gap with all gaps nonzero makes the RHS infinite. -/
public theorem infGap_rhs (C : ℝ) (hC : 0 < C)
    (hpos : ∀ j, gap j ν ≠ 0) (j : Fin d) (hinf : gap j ν = ∞) :
    ENNReal.ofReal C * ∏ j : Fin d, gap j ν = ∞ := by
  have hprod : (∏ j : Fin d, gap j ν) = ∞ :=
    prod_eq_top_aux Finset.univ _ j (Finset.mem_univ j) hinf
      (fun i _ => hpos i)
  rw [hprod]
  exact ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne'

end InfGap

section FinMom

variable {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
  [IsProbabilityMeasure ν] (j : Fin d)

/-- HI-FINMOM: finite gaps imply finite coordinate first absolute moments. -/
public theorem finite_gap_moment (hfin : gap j ν < ∞) :
    (∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν) < ∞ := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) :=
    measurable_coord j
  set μ : Measure ℝ := coordMarginal ν j with hμdef
  have hgap : (∫⁻ q : ℝ × ℝ, (‖q.1 - q.2‖₊ : ℝ≥0∞) ∂(μ.prod μ)) < ∞ := by
    rw [← gap_eq_marginal_gap ν j]
    exact hfin
  -- `g(a) = E|X - a|`.
  set g : ℝ → ℝ≥0∞ := fun a => ∫⁻ x, ((‖x - a‖₊ : ℝ≥0) : ℝ≥0∞) ∂μ
    with hgdef
  have hG : Measurable (fun p : ℝ × ℝ => ((‖p.2 - p.1‖₊ : ℝ≥0) : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp
      (measurable_snd.sub measurable_fst).nnnorm
  have hgm : Measurable g := by
    have hunc : Measurable (Function.uncurry
        (fun a x : ℝ => ((‖x - a‖₊ : ℝ≥0) : ℝ≥0∞))) := hG
    have h := Measurable.lintegral_prod_right (ν := μ) hunc
    simpa [hgdef, Function.uncurry] using h
  have hflip : ∀ p : ℝ × ℝ, ((‖p.2 - p.1‖₊ : ℝ≥0) : ℝ≥0∞)
      = ((‖p.1 - p.2‖₊ : ℝ≥0) : ℝ≥0∞) := by
    intro p
    congr 1
    exact Subtype.ext (norm_sub_rev _ _)
  have hEg : (∫⁻ a, g a ∂μ) < ∞ := by
    have hton : (∫⁻ a, g a ∂μ)
        = ∫⁻ q : ℝ × ℝ, (‖q.1 - q.2‖₊ : ℝ≥0∞) ∂(μ.prod μ) := by
      have hprod : (∫⁻ a, g a ∂μ)
          = ∫⁻ p : ℝ × ℝ, ((‖p.2 - p.1‖₊ : ℝ≥0) : ℝ≥0∞)
            ∂(μ.prod μ) := by
        rw [← lintegral_prod _ hG.aemeasurable]
      rw [hprod]
      apply lintegral_congr_ae
      filter_upwards with p
      exact hflip p
    rw [hton]
    exact hgap
  obtain ⟨a, ha⟩ : ∃ a, g a < ∞ := by
    have hae : ∀ᵐ a ∂μ, g a < ∞ := ae_lt_top hgm (ne_of_lt hEg)
    by_contra hcon
    rw [not_exists] at hcon
    have hfalse : ∀ᵐ _ ∂μ, False := hae.mono (fun x hx => hcon x hx)
    have hmem : {x : ℝ | False} ∈ ae μ := hfalse
    rw [mem_ae_iff] at hmem
    have hset : {x : ℝ | False}ᶜ = Set.univ := by simp
    have h1 : μ Set.univ = 1 := measure_univ
    rw [hset, h1] at hmem
    exact one_ne_zero hmem
  have hfinite : (∫⁻ x, ((‖x‖₊ : ℝ≥0) : ℝ≥0∞) ∂μ) < ∞ := by
    have htri : ∀ x : ℝ, ((‖x‖₊ : ℝ≥0) : ℝ≥0∞)
        ≤ ((‖x - a‖₊ : ℝ≥0) : ℝ≥0∞) + ((‖a‖₊ : ℝ≥0) : ℝ≥0∞) := by
      intro x
      have h := nnnorm_add_le (x - a) a
      rw [sub_add_cancel] at h
      exact_mod_cast h
    have hmeas1 : Measurable
        (fun x : ℝ => ((‖x - a‖₊ : ℝ≥0) : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp
        ((measurable_id.sub measurable_const).nnnorm)
    have hle : (∫⁻ x, ((‖x‖₊ : ℝ≥0) : ℝ≥0∞) ∂μ)
        ≤ g a + ((‖a‖₊ : ℝ≥0) : ℝ≥0∞) := by
      calc (∫⁻ x, ((‖x‖₊ : ℝ≥0) : ℝ≥0∞) ∂μ)
          ≤ ∫⁻ x, (((‖x - a‖₊ : ℝ≥0) : ℝ≥0∞)
            + ((‖a‖₊ : ℝ≥0) : ℝ≥0∞)) ∂μ := by
              apply lintegral_mono_ae
              filter_upwards with x
              exact htri x
        _ = (∫⁻ x, ((‖x - a‖₊ : ℝ≥0) : ℝ≥0∞) ∂μ)
            + ∫⁻ _, ((‖a‖₊ : ℝ≥0) : ℝ≥0∞) ∂μ :=
              lintegral_add_left hmeas1 _
        _ = g a + ((‖a‖₊ : ℝ≥0) : ℝ≥0∞) := by
              have hga : (∫⁻ x, ((‖x - a‖₊ : ℝ≥0) : ℝ≥0∞) ∂μ) = g a := rfl
              rw [lintegral_const, measure_univ, mul_one, hga]
    exact lt_of_le_of_lt hle
      (ENNReal.add_lt_top.mpr ⟨ha, ENNReal.coe_lt_top⟩)
  have hback : (∫⁻ x, ((‖x‖₊ : ℝ≥0) : ℝ≥0∞) ∂μ)
      = ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν := by
    have hF : Measurable (fun y : ℝ => ((‖y‖₊ : ℝ≥0) : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp measurable_id.nnnorm
    rw [hμdef]
    simp only [coordMarginal]
    exact lintegral_map hF hmeas
  rw [← hback]
  exact hfinite

end FinMom

section ZeroGap

open scoped InnerProductSpace

variable {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
  [IsProbabilityMeasure ν] (j : Fin d)

/-- Vanishing gap: almost every pair shares its `j`th coordinate. -/
private theorem ae_eq_coord_of_gap_eq_zero (hgap : gap j ν = 0) :
    ∀ᵐ p ∂(ν.prod ν), p.1 j = p.2 j := by
  have h0 : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (‖p.1 j - p.2 j‖₊ : ℝ≥0∞)) =ᵐ[ν.prod ν] 0 :=
    (lintegral_eq_zero_iff (measurable_gap_integrand j)).mp
      (by simpa [gap] using hgap)
  filter_upwards [h0] with p hp
  simp only [Pi.zero_apply] at hp
  rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero, sub_eq_zero] at hp

/-- The off-diagonal is null for the product of coordinate marginals. -/
private theorem prod_marginal_offdiag_null (hgap : gap j ν = 0) :
    ((coordMarginal ν j).prod (coordMarginal ν j))
      {q : ℝ × ℝ | q.1 ≠ q.2} = 0 := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) :=
    measurable_coord j
  have hAe := ae_eq_coord_of_gap_eq_zero ν j hgap
  have hnull : (ν.prod ν)
      {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
        p.1 j ≠ p.2 j} = 0 := by
    have hmem : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
        p.1 j = p.2 j} ∈ ae (ν.prod ν) := hAe
    have h0 := mem_ae_iff.mp hmem
    have hset : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
        p.1 j ≠ p.2 j}
        = {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
          p.1 j = p.2 j}ᶜ := by
      ext p
      simp
    rw [hset]
    exact h0
  have hmap := Measure.map_prod_map ν ν hmeas hmeas
  have hme : Measurable (Prod.map (fun x : EuclideanSpace ℝ (Fin d) => x j)
      (fun x : EuclideanSpace ℝ (Fin d) => x j)) :=
    hmeas.prodMap hmeas
  have hdiag : MeasurableSet {q : ℝ × ℝ | q.1 ≠ q.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  simp only [coordMarginal]
  rw [hmap, Measure.map_apply hme hdiag]
  exact hnull

/-- Two-coordinate cylinders factor over distinct coordinates. -/
private theorem pi_two_cyl (a b : Fin (d + 1)) (hab : a ≠ b)
    (s t : Set (EuclideanSpace ℝ (Fin d))) :
    (Measure.pi (fun _ : Fin (d + 1) => ν))
        {Z | Z a ∈ s ∧ Z b ∈ t} = ν s * ν t := by
  have hba : b ≠ a := fun h => hab h.symm
  set F : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)) :=
    fun i => if i = a then s else if i = b then t else Set.univ with hFdef
  have hFa : F a = s := by simp [hFdef]
  have hFb : F b = t := by simp [hFdef, hba]
  have hset : {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
      Z a ∈ s ∧ Z b ∈ t} = Set.pi Set.univ F := by
    ext Z
    show (Z a ∈ s ∧ Z b ∈ t) ↔ Z ∈ Set.pi Set.univ F
    constructor
    · rintro ⟨ha, hb⟩
      rw [Set.mem_pi]
      intro i _
      by_cases hi : i = a
      · subst hi
        simpa [hFdef] using ha
      · by_cases hi2 : i = b
        · subst hi2
          simpa [hFdef, hi] using hb
        · simp [hFdef, hi, hi2]
    · intro h
      rw [Set.mem_pi] at h
      refine ⟨?_, ?_⟩
      · have ha := h a (Set.mem_univ a)
        simpa [hFdef] using ha
      · have hb := h b (Set.mem_univ b)
        simpa [hFdef, hba] using hb
  rw [hset, Measure.pi_pi]
  change ∏ i, ν (F i) = ν s * ν t
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), hFa,
    ← Finset.mul_prod_erase _ _
      (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩), hFb]
  have hrest : ∏ x ∈ (Finset.univ.erase a).erase b, ν (F x) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    obtain ⟨hxb, hx2⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxa, _⟩ := Finset.mem_erase.mp hx2
    have hFx : F x = Set.univ := by simp [hFdef, hxa, hxb]
    rw [hFx, measure_univ]
  rw [hrest, mul_one]

/-- Off-diagonal pairs are null in the simplex sample measure. -/
private theorem pair_offdiag_null (a b : Fin (d + 1)) (hab : a ≠ b)
    (hgap : gap j ν = 0) :
    (Measure.pi (fun _ : Fin (d + 1) => ν))
      {Z | Z a j ≠ Z b j} = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) :=
    measurable_coord j
  have hlt : ∀ q : ℚ, MeasurableSet {x : ℝ | x < (q : ℝ)} := fun _ =>
    measurableSet_lt measurable_id measurable_const
  have hle : ∀ q : ℚ, MeasurableSet {x : ℝ | (q : ℝ) ≤ x} := fun _ =>
    measurableSet_le measurable_const measurable_id
  have hC0 : ∀ q : ℚ, (Measure.pi (fun _ : Fin (d + 1) => ν))
      {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
        Z a j < (q : ℝ) ∧ (q : ℝ) ≤ Z b j} = 0 := by
    intro q
    have hcyl := pi_two_cyl ν a b hab
      {u : EuclideanSpace ℝ (Fin d) | u j < (q : ℝ)}
      {u : EuclideanSpace ℝ (Fin d) | (q : ℝ) ≤ u j}
    have hset : {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
        Z a j < (q : ℝ) ∧ (q : ℝ) ≤ Z b j}
        = {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
          Z a ∈ {u : EuclideanSpace ℝ (Fin d) | u j < (q : ℝ)} ∧
          Z b ∈ {u : EuclideanSpace ℝ (Fin d) | (q : ℝ) ≤ u j}} := rfl
    rw [hset, hcyl]
    have hms : ν {u : EuclideanSpace ℝ (Fin d) | u j < (q : ℝ)}
        = coordMarginal ν j {x : ℝ | x < (q : ℝ)} := by
      unfold coordMarginal
      exact (Measure.map_apply hmeas (hlt q)).symm
    have hmt : ν {u : EuclideanSpace ℝ (Fin d) | (q : ℝ) ≤ u j}
        = coordMarginal ν j {x : ℝ | (q : ℝ) ≤ x} := by
      unfold coordMarginal
      exact (Measure.map_apply hmeas (hle q)).symm
    rw [hms, hmt, ← Measure.prod_prod]
    apply measure_mono_null _ (prod_marginal_offdiag_null ν j hgap)
    intro p hp
    simp only [Set.mem_prod, Set.mem_ofPred_eq] at hp ⊢
    exact ne_of_lt (lt_of_lt_of_le hp.1 hp.2)
  have hD0 : ∀ q : ℚ, (Measure.pi (fun _ : Fin (d + 1) => ν))
      {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
        Z b j < (q : ℝ) ∧ (q : ℝ) ≤ Z a j} = 0 := by
    intro q
    have hcyl := pi_two_cyl ν b a hba
      {u : EuclideanSpace ℝ (Fin d) | u j < (q : ℝ)}
      {u : EuclideanSpace ℝ (Fin d) | (q : ℝ) ≤ u j}
    have hset : {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
        Z b j < (q : ℝ) ∧ (q : ℝ) ≤ Z a j}
        = {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
          Z b ∈ {u : EuclideanSpace ℝ (Fin d) | u j < (q : ℝ)} ∧
          Z a ∈ {u : EuclideanSpace ℝ (Fin d) | (q : ℝ) ≤ u j}} := rfl
    rw [hset, hcyl]
    have hms : ν {u : EuclideanSpace ℝ (Fin d) | u j < (q : ℝ)}
        = coordMarginal ν j {x : ℝ | x < (q : ℝ)} := by
      unfold coordMarginal
      exact (Measure.map_apply hmeas (hlt q)).symm
    have hmt : ν {u : EuclideanSpace ℝ (Fin d) | (q : ℝ) ≤ u j}
        = coordMarginal ν j {x : ℝ | (q : ℝ) ≤ x} := by
      unfold coordMarginal
      exact (Measure.map_apply hmeas (hle q)).symm
    rw [hms, hmt, ← Measure.prod_prod]
    apply measure_mono_null _ (prod_marginal_offdiag_null ν j hgap)
    intro p hp
    simp only [Set.mem_prod, Set.mem_ofPred_eq] at hp ⊢
    exact ne_of_lt (lt_of_lt_of_le hp.1 hp.2)
  have hcover : {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
      Z a j ≠ Z b j}
      ⊆ ⋃ q : ℚ, ({Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
        Z a j < (q : ℝ) ∧ (q : ℝ) ≤ Z b j} ∪
        {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
          Z b j < (q : ℝ) ∧ (q : ℝ) ≤ Z a j}) := by
    intro Z hZ
    simp only [Set.mem_ofPred_eq] at hZ
    by_cases hlt : Z a j < Z b j
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      exact Set.mem_iUnion.mpr ⟨q, Or.inl ⟨hq1, le_of_lt hq2⟩⟩
    · have hle : Z b j ≤ Z a j := le_of_not_gt hlt
      have hne : Z b j ≠ Z a j := Ne.symm hZ
      have hlt' : Z b j < Z a j := lt_of_le_of_ne hle hne
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
      exact Set.mem_iUnion.mpr ⟨q, Or.inr ⟨hq1, le_of_lt hq2⟩⟩
  have hU0 : ∀ q : ℚ, (Measure.pi (fun _ : Fin (d + 1) => ν))
      ({Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
        Z a j < (q : ℝ) ∧ (q : ℝ) ≤ Z b j} ∪
        {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
          Z b j < (q : ℝ) ∧ (q : ℝ) ≤ Z a j}) = 0 := by
    intro q
    refine le_antisymm ?_ zero_le
    refine le_trans (measure_union_le _ _) ?_
    simp [hC0 q, hD0 q]
  refine measure_mono_null hcover ?_
  refine le_antisymm ?_ zero_le
  refine le_trans (measure_iUnion_le _) ?_
  simp [hU0]

/-- All simplex vertices share their `j`th coordinate almost surely. -/
private theorem ae_all_eq_coord (hgap : gap j ν = 0) :
    ∀ᵐ Z ∂(Measure.pi (fun _ : Fin (d + 1) => ν)),
      ∀ a b, Z a j = Z b j := by
  rw [ae_all_iff]
  intro a
  rw [ae_all_iff]
  intro b
  by_cases hab : a = b
  · subst hab
    exact Filter.Eventually.of_forall fun Z => rfl
  · have h0 := pair_offdiag_null ν j a b hab hgap
    have hset : {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
        Z a j = Z b j}ᶜ
        = {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
          Z a j ≠ Z b j} := by
      ext Z
      simp
    have hmem : {Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d) |
        Z a j = Z b j} ∈ ae (Measure.pi (fun _ : Fin (d + 1) => ν)) := by
      rw [mem_ae_iff, hset]
      exact h0
    exact hmem

/-- The hull of coordinate-flat samples is null. -/
private theorem hull_null_of_all_eq
    (Z : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
    (hZ : ∀ a b, Z a j = Z b j) :
    volume (convexHull ℝ (Set.range Z)) = 0 := by
  set H : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
    { carrier := {v | ⟪EuclideanSpace.single j (1 : ℝ), v⟫_ℝ = 0},
      zero_mem' := by
        show ⟪EuclideanSpace.single j (1 : ℝ),
          (0 : EuclideanSpace ℝ (Fin d))⟫_ℝ = 0
        exact inner_zero_right _,
      add_mem' := by
        intro x y hx hy
        show ⟪EuclideanSpace.single j (1 : ℝ), x + y⟫_ℝ = 0
        rw [inner_add_right,
          show ⟪EuclideanSpace.single j (1 : ℝ), x⟫_ℝ = 0 from hx,
          show ⟪EuclideanSpace.single j (1 : ℝ), y⟫_ℝ = 0 from hy,
          add_zero],
      smul_mem' := by
        intro r x hx
        show ⟪EuclideanSpace.single j (1 : ℝ), r • x⟫_ℝ = 0
        rw [inner_smul_right,
          show ⟪EuclideanSpace.single j (1 : ℝ), x⟫_ℝ = 0 from hx,
          mul_zero] } with hHdef
  have hHmem : ∀ v : EuclideanSpace ℝ (Fin d),
      v ∈ (↑H : Set (EuclideanSpace ℝ (Fin d))) ↔
        ⟪EuclideanSpace.single j (1 : ℝ), v⟫_ℝ = 0 := fun v => Iff.rfl
  have hℓ : ∀ a, ⟪EuclideanSpace.single j (1 : ℝ), Z a⟫_ℝ = Z a j := by
    intro a
    rw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]
  have h1 : ⟪EuclideanSpace.single j (1 : ℝ),
      EuclideanSpace.single j (1 : ℝ)⟫_ℝ = 1 := by
    simp [EuclideanSpace.single]
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hmem : EuclideanSpace.single j (1 : ℝ) ∈ H := by
      rw [htop]
      exact Submodule.mem_top
    have hmemU : EuclideanSpace.single j (1 : ℝ)
        ∈ (↑H : Set (EuclideanSpace ℝ (Fin d))) := hmem
    have hmem' : ⟪EuclideanSpace.single j (1 : ℝ),
        EuclideanSpace.single j (1 : ℝ)⟫_ℝ = 0 := (hHmem _).mp hmemU
    rw [h1] at hmem'
    exact one_ne_zero hmem'
  have hdir : (affineSpan ℝ (Set.range Z)).direction ≤ H := by
    rw [direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℝ
        (Set.mem_range_self (0 : Fin (d + 1)) : Z 0 ∈ Set.range Z),
      Submodule.span_le]
    intro v hv
    obtain ⟨w, hw, hfw⟩ := hv
    obtain ⟨a, rfl⟩ := hw
    subst hfw
    show Z a -ᵥ Z 0 ∈ (↑H : Set (EuclideanSpace ℝ (Fin d)))
    have heq : ⟪EuclideanSpace.single j (1 : ℝ), Z a -ᵥ Z 0⟫_ℝ = 0 := by
      rw [vsub_eq_sub, inner_sub_right, hℓ a, hℓ 0, hZ a 0, sub_self]
    exact (hHmem _).mpr heq
  have hne : ((affineSpan ℝ (Set.range Z) :
      Set (EuclideanSpace ℝ (Fin d)))).Nonempty :=
    ⟨Z 0, subset_affineSpan ℝ _
      (Set.mem_range_self (0 : Fin (d + 1)) : Z 0 ∈ Set.range Z)⟩
  have hAtop : affineSpan ℝ (Set.range Z) ≠ ⊤ := by
    intro hcon
    apply hHtop
    have hdirtop : (affineSpan ℝ (Set.range Z)).direction = ⊤ := by
      rw [AffineSubspace.direction_eq_top_iff_of_nonempty hne]
      exact hcon
    have htop : (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) ≤ H := by
      rw [← hdirtop]
      exact hdir
    exact top_le_iff.mp htop
  have hsub : convexHull ℝ (Set.range Z)
      ⊆ ↑(affineSpan ℝ (Set.range Z)) := by
    have h := subset_affineSpan ℝ (convexHull ℝ (Set.range Z))
    rw [affineSpan_convexHull] at h
    exact h
  have hvol := Measure.addHaar_affineSubspace volume _ hAtop
  exact measure_mono_null hsub hvol

/-- HI-ZERO: a vanishing coordinate gap forces a null simplex functional. -/
public theorem gap_eq_zero_imp_S_eq_zero (hgap : gap j ν = 0) : S d ν = 0 := by
  have hAe := ae_all_eq_coord ν j hgap
  have hvol0 : ∀ᵐ Z ∂(Measure.pi (fun _ : Fin (d + 1) => ν)),
      volume (convexHull ℝ (Set.range Z)) = 0 := by
    filter_upwards [hAe] with Z hZ
    exact hull_null_of_all_eq j Z hZ
  have hSeq : S d ν
      = ∫⁻ _ : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
        0 ∂(Measure.pi (fun _ : Fin (d + 1) => ν)) := by
    simp only [S]
    exact lintegral_congr_ae hvol0
  rw [hSeq]
  exact lintegral_zero

end ZeroGap

section Quant

variable {d : ℕ}

/-- Coordinate quantization `φ_n` (Sec7): clip to `[-n,n]`, round down to the `1/n` grid. -/
@[expose] public noncomputable def quantFn (n : ℕ) (t : ℝ) : ℝ :=
  max (-(n : ℝ)) (min (n : ℝ) (((⌊(n : ℝ) * t⌋ : ℤ) : ℝ) / (n : ℝ)))

/-- Splitting `n < |t|` by sign. -/
private theorem lt_abs_split (n : ℕ) (t : ℝ) (h : (n : ℝ) < |t|) :
    (n : ℝ) < t ∨ t < (-(n : ℝ)) := by
  rcases le_total 0 t with hnn | hnp
  · left
    rwa [abs_of_nonneg hnn] at h
  · right
    rcases eq_or_ne t 0 with rfl | ht0
    · simp at h
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    · have habs : |t| = -t := abs_of_neg (lt_of_le_of_ne hnp ht0)
      linarith

/-- The grid point lies in `[-n,n]` when `|t| ≤ n`. -/
private theorem grid_mem_Icc_of_abs_le (n : ℕ) (t : ℝ) (h : |t| ≤ (n : ℝ)) :
    (-(n : ℝ)) ≤ (((⌊(n : ℝ) * t⌋ : ℤ) : ℝ) / (n : ℝ))
      ∧ (((⌊(n : ℝ) * t⌋ : ℤ) : ℝ) / (n : ℝ)) ≤ (n : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have ht : t = 0 := by
      have h0 : |t| ≤ 0 := by simpa using h
      have h1 : |t| = 0 := le_antisymm h0 (abs_nonneg t)
      rwa [abs_eq_zero] at h1
    subst ht
    simp [Int.floor_zero]
  · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnnon : (0:ℝ) ≤ (n:ℝ) := le_of_lt hnpos
    constructor
    · rw [le_div_iff₀ hnpos]
      have hx : (-((n:ℝ))^2) ≤ (n:ℝ)*t := by
        have h1 : (-((n:ℝ)) * |t|) ≤ (n:ℝ)*t := by
          have h3 := mul_le_mul_of_nonneg_left
            ((abs_le.mp le_rfl).1 : (-|t|) ≤ t) hnnon
          have heq : (-((n:ℝ))) * |t| = (n:ℝ) * (-|t|) := by ring
          rw [heq]
          exact h3
        have h2 : (-((n:ℝ))^2) ≤ (-((n:ℝ)) * |t|) := by
          have hnt : (n:ℝ)*|t| ≤ (n:ℝ)*(n:ℝ) :=
            mul_le_mul_of_nonneg_left h hnnon
          have hsq : ((n:ℝ))^2 = (n:ℝ)*(n:ℝ) := pow_two _
          have heq2 : (-((n:ℝ))) * |t| = -((n:ℝ)*|t|) := by ring
          rw [hsq, heq2]
          exact neg_le_neg hnt
        exact le_trans h2 h1
      have hkr : (-((n:ℝ))^2) ≤ ((⌊(n:ℝ)*t⌋ : ℤ) : ℝ) := by
        have h1 := Int.floor_mono hx
        have hcast : (-((n:ℝ))^2) = (((-(((n:ℤ)^2)) : ℤ)) : ℝ) := by
          push_cast
          ring
        rw [hcast, Int.floor_intCast] at h1
        rw [hcast]
        exact Int.cast_le.mpr h1
      have hsq : (-((n:ℝ)))*(n:ℝ) = (-((n:ℝ))^2) := by ring
      rw [hsq]
      exact hkr
    · rw [div_le_iff₀ hnpos]
      have h1 : ((⌊(n:ℝ)*t⌋ : ℤ) : ℝ) ≤ (n:ℝ)*t := Int.floor_le _
      have h2a : (n:ℝ)*t ≤ (n:ℝ)*|t| :=
        mul_le_mul_of_nonneg_left (le_abs_self t) hnnon
      have h2b : (n:ℝ)*|t| ≤ (n:ℝ)*(n:ℝ) :=
        mul_le_mul_of_nonneg_left h hnnon
      exact le_trans h1 (le_trans h2a h2b)

/-- Inside `[-n,n]`, no clipping occurs. -/
public theorem quantFn_eq_of_abs_le (n : ℕ) (t : ℝ) (h : |t| ≤ (n : ℝ)) :
    quantFn n t = (((⌊(n : ℝ) * t⌋ : ℤ) : ℝ) / (n : ℝ)) := by
  have hmem := grid_mem_Icc_of_abs_le n t h
  simp only [quantFn]
  rw [min_eq_right hmem.2, max_eq_right hmem.1]

/-- Above `n`, the quantizer clips to `n`. -/
public theorem quantFn_eq_of_gt (n : ℕ) (t : ℝ) (h : (n : ℝ) < t) :
    quantFn n t = (n : ℝ) := by
  simp only [quantFn]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Int.floor_zero]
  · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hge : (n:ℝ) ≤ (((⌊(n:ℝ)*t⌋ : ℤ) : ℝ) / (n:ℝ)) := by
      rw [le_div_iff₀ hnpos]
      have hnt : (n:ℝ)*(n:ℝ) ≤ (n:ℝ)*t :=
        le_of_lt (mul_lt_mul_of_pos_left h hnpos)
      have hcast : ((((n:ℤ)^2) : ℤ) : ℝ) = (n:ℝ)*(n:ℝ) := by
        push_cast
        ring
      have hfl : ((n:ℤ)^2) ≤ ⌊(n:ℝ)*t⌋ := by
        have h1 := Int.floor_mono hnt
        rw [← hcast, Int.floor_intCast] at h1
        exact h1
      rw [← hcast]
      exact Int.cast_le.mpr hfl
    have hnn : (-(n:ℝ)) ≤ (n:ℝ) := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    rw [min_eq_left hge, max_eq_right hnn]

/-- Below `-n`, the quantizer clips to `-n`. -/
public theorem quantFn_eq_of_lt (n : ℕ) (t : ℝ) (h : t < (-(n : ℝ))) :
    quantFn n t = (-(n : ℝ)) := by
  simp only [quantFn]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Int.floor_zero]
  · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hle : (((⌊(n:ℝ)*t⌋ : ℤ) : ℝ)/(n:ℝ)) < (-(n:ℝ)) := by
      rw [div_lt_iff₀ hnpos]
      have h1 : ((⌊(n:ℝ)*t⌋ : ℤ) : ℝ) ≤ (n:ℝ)*t := Int.floor_le _
      have hnt : (n:ℝ)*t < (n:ℝ)*(-(n:ℝ)) :=
        mul_lt_mul_of_pos_left h hnpos
      have h2 : (n:ℝ)*(-(n:ℝ)) = (-(n:ℝ))*(n:ℝ) := by ring
      linarith [h1, hnt, h2]
    have hle' := le_of_lt hle
    have hnn : (-(n:ℝ)) ≤ (n:ℝ) := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    rw [min_eq_right (le_trans hle' hnn), max_eq_left hle']

/-- Grid rounding error (no clipping). -/
private theorem grid_round_le (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    |((⌊(n : ℝ) * t⌋ : ℤ) : ℝ) / (n : ℝ) - t| ≤ 1 / (n : ℝ) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn' : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  have heq : ((⌊(n : ℝ) * t⌋ : ℤ) : ℝ) / (n : ℝ) - t
      = (((⌊(n : ℝ) * t⌋ : ℤ) : ℝ) - (n:ℝ)*t)/(n:ℝ) := by
    field_simp
  have hk1 : ((⌊(n : ℝ) * t⌋ : ℤ) : ℝ) ≤ (n:ℝ)*t := Int.floor_le _
  have hk2 : (n:ℝ)*t < (((⌊(n : ℝ) * t⌋ : ℤ) : ℝ)) + 1 :=
    Int.lt_floor_add_one _
  have hside : ((⌊(n:ℝ)*t⌋:ℤ):ℝ) - (n:ℝ)*t ≤ 0 := by linarith [hk1]
  have hle : |((⌊(n:ℝ)*t⌋:ℤ):ℝ) - (n:ℝ)*t| ≤ 1 := by
    rw [abs_of_nonpos hside]
    linarith [hk2]
  rw [heq, abs_div, abs_of_pos hnpos]
  simp only [div_eq_mul_inv, one_mul]
  have hpos : (0:ℝ) ≤ ((n:ℝ))⁻¹ := le_of_lt (inv_pos.mpr hnpos)
  have h2 := mul_le_mul_of_nonneg_right hle hpos
  rwa [one_mul] at h2

/-- Manuscript quantization error bound. -/
public theorem quantFn_bound (n : ℕ) (t : ℝ) :
    |quantFn n t - t|
      ≤ 1/(n:ℝ) + |t| * (if (n:ℝ) < |t| then (1:ℝ) else 0) := by
  by_cases h : |t| ≤ (n:ℝ)
  · have hif : (if (n:ℝ) < |t| then (1:ℝ) else 0) = 0 := ite_eq_right (not_lt.mpr h)
    rw [quantFn_eq_of_abs_le n t h, hif, mul_zero, add_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · have ht : t = 0 := by
        have h0 : |t| ≤ 0 := by simpa using h
        have h1 : |t| = 0 := le_antisymm h0 (abs_nonneg t)
        rwa [abs_eq_zero] at h1
      subst ht
      simp [Int.floor_zero]
    · exact grid_round_le n hn t
  · have hlt : (n:ℝ) < |t| := lt_of_not_ge h
    have hif : (if (n:ℝ) < |t| then (1:ℝ) else 0) = 1 := ite_eq_left hlt
    rw [hif, mul_one]
    have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h3 : (0:ℝ) ≤ 1/(n:ℝ) := div_nonneg zero_le_one hnn
    obtain (hgt | hlt') := lt_abs_split n t hlt
    · rw [quantFn_eq_of_gt n t hgt]
      have h1 : |t| = t :=
        abs_of_nonneg (le_of_lt (lt_of_le_of_lt hnn hgt))
      have h2 : |(n:ℝ) - t| = t - (n:ℝ) := by
        rw [abs_of_neg (by linarith : (n:ℝ) - t < 0), neg_sub]
      rw [h2, h1]
      linarith
    · rw [quantFn_eq_of_lt n t hlt']
      have h1 : |t| = -t := abs_of_neg (by linarith : t < 0)
      have h2 : |(-(n:ℝ)) - t| = (-(n:ℝ)) - t :=
        abs_of_nonneg (by linarith : (0:ℝ) ≤ (-(n:ℝ)) - t)
      rw [h2, h1]
      linarith

/-- Uniform moment bound for the quantizer. -/
public theorem quantFn_abs_le (n : ℕ) (t : ℝ) : |quantFn n t| ≤ |t| + 1 := by
  by_cases h : |t| ≤ (n:ℝ)
  · rw [quantFn_eq_of_abs_le n t h]
    rcases eq_or_ne n 0 with rfl | hn
    · have ht : t = 0 := by
        have h0 : |t| ≤ 0 := by simpa using h
        have h1 : |t| = 0 := le_antisymm h0 (abs_nonneg t)
        rwa [abs_eq_zero] at h1
      subst ht
      simp [Int.floor_zero]
    · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hgrid := grid_round_le n hn t
      have h1d : (1:ℝ)/(n:ℝ) ≤ 1 := by
        rw [div_le_iff₀ hnpos, one_mul]
        exact hn1
      have h2 := abs_sub_abs_le_abs_sub
        (((⌊(n:ℝ)*t⌋:ℤ):ℝ)/(n:ℝ)) t
      linarith [hgrid, h1d, h2]
  · have hlt : (n:ℝ) < |t| := lt_of_not_ge h
    obtain (hgt | hlt') := lt_abs_split n t hlt
    · rw [quantFn_eq_of_gt n t hgt, abs_of_nonneg (Nat.cast_nonneg n)]
      have : (0:ℝ) ≤ (1:ℝ) := zero_le_one
      linarith [hlt]
    · rw [quantFn_eq_of_lt n t hlt', abs_neg,
        abs_of_nonneg (Nat.cast_nonneg n)]
      have : (0:ℝ) ≤ (1:ℝ) := zero_le_one
      linarith [hlt]

/-- The quantizer is measurable. -/
public theorem measurable_quantFn (n : ℕ) : Measurable (quantFn n) := by
  have hfloor : Measurable (fun t : ℝ => ⌊(n:ℝ)*t⌋) :=
    Int.measurable_floor.comp (measurable_const_mul _)
  have hcast : Measurable (Int.cast : ℤ → ℝ) :=
    continuous_of_discreteTopology.measurable
  have hgrid : Measurable
      (fun t : ℝ => (((⌊(n:ℝ)*t⌋ : ℤ) : ℝ))/(n:ℝ)) :=
    (hcast.comp hfloor).div_const _
  have hc1 : Measurable (fun _ : ℝ => (n:ℝ)) := measurable_const
  have hc2 : Measurable (fun _ : ℝ => (-(n:ℝ))) := measurable_const
  have hmin : Measurable
      (fun t : ℝ => min (n:ℝ) ((((⌊(n:ℝ)*t⌋ : ℤ) : ℝ))/(n:ℝ))) :=
    hc1.min hgrid
  have hmax : Measurable (fun t : ℝ =>
      max (-(n:ℝ)) (min (n:ℝ) ((((⌊(n:ℝ)*t⌋ : ℤ) : ℝ))/(n:ℝ)))) :=
    hc2.max hmin
  exact hmax

/-- The quantizer has finite range. -/
public theorem quantFn_range_finite (n : ℕ) :
    (Set.range (quantFn n)).Finite := by
  classical
  set S : Finset ℝ :=
    Finset.image (fun k : ℤ => ((k : ℝ))/(n:ℝ))
        (Finset.Icc (-((n:ℤ)^2)) ((n:ℤ)^2))
      ∪ {-((n:ℝ)), (n:ℝ)} with hSdef
  have hfin : (↑S : Set ℝ).Finite := Finset.finite_toSet S
  apply Set.Finite.subset hfin
  intro y hy
  obtain ⟨t, rfl⟩ := hy
  rw [hSdef, Finset.mem_coe]
  by_cases h : |t| ≤ (n:ℝ)
  · rw [quantFn_eq_of_abs_le n t h]
    have hmem := grid_mem_Icc_of_abs_le n t h
    have hi : ⌊(n:ℝ)*t⌋ ≤ ((n:ℤ)^2) := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp [Int.floor_zero]
      · have hnpos : (0:ℝ) < (n:ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        have h1 : ((⌊(n:ℝ)*t⌋ : ℤ) : ℝ) ≤ (n:ℝ)*(n:ℝ) :=
          (div_le_iff₀ hnpos).mp hmem.2
        have hcast : ((((n:ℤ)^2) : ℤ) : ℝ) = (n:ℝ)*(n:ℝ) := by
          push_cast
          ring
        rw [← hcast] at h1
        exact Int.cast_le.mp h1
    have lo : (-(((n:ℤ)^2))) ≤ ⌊(n:ℝ)*t⌋ := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp [Int.floor_zero]
      · have hnpos : (0:ℝ) < (n:ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        have h1 : (-(n:ℝ))*(n:ℝ) ≤ ((⌊(n:ℝ)*t⌋ : ℤ) : ℝ) :=
          (le_div_iff₀ hnpos).mp hmem.1
        have hcast : (((-(((n:ℤ)^2)) : ℤ)) : ℝ) = (-(n:ℝ))*(n:ℝ) := by
          push_cast
          ring
        rw [← hcast] at h1
        exact Int.cast_le.mp h1
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
      ⟨⌊(n:ℝ)*t⌋, Finset.mem_Icc.mpr ⟨lo, hi⟩, rfl⟩))
  · have hlt : (n:ℝ) < |t| := lt_of_not_ge h
    obtain (hgt | hlt') := lt_abs_split n t hlt
    · rw [quantFn_eq_of_gt n t hgt]
      exact Finset.mem_union.mpr (Or.inr (by simp))
    · rw [quantFn_eq_of_lt n t hlt']
      exact Finset.mem_union.mpr (Or.inr (by simp))

/-- Tail integrand for the L1 estimate. -/
private noncomputable def tailInd (j : Fin d) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  Set.indicator {x | (n:ℝ) < |x j|} (fun x => ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞)) x

private theorem measurable_tailInd_base (j : Fin d) :
    Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
      ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞)) :=
  measurable_coe_nnreal_ennreal.comp (measurable_coord j).nnnorm

private theorem measurableSet_tailInd_set (j : Fin d) (n : ℕ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin d) | (n:ℝ) < |x j|} :=
  measurableSet_lt measurable_const ((measurable_coord j).abs)

/-- The tail integral vanishes. -/
private theorem tail_tendsto_zero (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (j : Fin d)
    (hmom : ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞) :
    Tendsto (fun n : ℕ => ∫⁻ x, tailInd j n x ∂ν) atTop (𝓝 0) := by
  have hf : ∀ n : ℕ, AEMeasurable (fun x => tailInd j n x) ν := by
    intro n
    exact ((measurable_tailInd_base j).indicator
      (measurableSet_tailInd_set j n)).aemeasurable
  have h_anti : ∀ᵐ x ∂ν, Antitone fun n => tailInd j n x := by
    filter_upwards with x
    intro n m hnm
    simp only [tailInd]
    by_cases hm : x ∈ {x : EuclideanSpace ℝ (Fin d) | (m:ℝ) < |x j|}
    · have hn : x ∈ {x : EuclideanSpace ℝ (Fin d) | (n:ℝ) < |x j|} := by
        simp only [Set.mem_ofPred_eq] at hm ⊢
        have hnm' : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
        linarith [hm]
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hn]
    · rw [Set.indicator_of_notMem hm]
      exact zero_le
  have h0 : ∫⁻ x, tailInd j 0 x ∂ν ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt _ (lt_top_iff_ne_top.mpr hmom)
    apply lintegral_mono
    intro x
    simp only [tailInd]
    by_cases hx : x ∈ {x : EuclideanSpace ℝ (Fin d) | (((0:ℕ)):ℝ) < |x j|}
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have h_tendsto : ∀ᵐ x ∂ν, Tendsto (fun n => tailInd j n x) atTop (𝓝 0) := by
    filter_upwards with x
    apply tendsto_atTop_of_eventually_const (i₀ := ⌈|x j|⌉₊)
    intro n hn
    simp only [tailInd]
    apply Set.indicator_of_notMem
    simp only [Set.mem_ofPred_eq, not_lt]
    have h1 : ((⌈|x j|⌉₊ : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have h2 : |x j| ≤ ((⌈|x j|⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith [h1, h2]
  have hlim := lintegral_tendsto_of_tendsto_of_antitone hf h_anti h0 h_tendsto
  rwa [lintegral_zero] at hlim

/-- L1 convergence of the coordinate quantization. -/
private theorem quant_l1_tendsto (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (j : Fin d)
    (hmom : ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞) :
    Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal |quantFn n (x j) - x j| ∂ν)
      atTop (𝓝 0) := by
  have hpt : ∀ n : ℕ, ∀ x : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal |quantFn n (x j) - x j|
        ≤ ENNReal.ofReal (1/(n:ℝ)) + tailInd j n x := by
    intro n x
    have hb := quantFn_bound n (x j)
    have h1 : (0:ℝ) ≤ 1/(n:ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg n)
    have h2 : (0:ℝ) ≤ |x j| * (if (n:ℝ) < |x j| then (1:ℝ) else 0) :=
      mul_nonneg (abs_nonneg _) (by split_ifs <;> simp)
    have hmono := ENNReal.ofReal_le_ofReal hb
    rw [ENNReal.ofReal_add h1 h2] at hmono
    have hind : ENNReal.ofReal (|x j| * (if (n:ℝ) < |x j| then (1:ℝ) else 0))
        = tailInd j n x := by
      simp only [tailInd]
      split_ifs with h'
      · rw [mul_one]
        have hco : |x j| = ((((‖x j‖₊ : ℝ≥0))) : ℝ) := by
          rw [coe_nnnorm, Real.norm_eq_abs]
        rw [hco, ENNReal.ofReal_coe_nnreal]
        have hmem : x ∈ {x : EuclideanSpace ℝ (Fin d) | (n:ℝ) < |x j|} := h'
        exact (Set.indicator_of_mem hmem
          (fun x => ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞))).symm
      · have h0 : |x j| * (0:ℝ) = 0 := by simp
        rw [h0, ENNReal.ofReal_zero]
        have hmem : x ∉ {x : EuclideanSpace ℝ (Fin d) | (n:ℝ) < |x j|} := h'
        exact (Set.indicator_of_notMem hmem
          (fun x => ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞))).symm
    rw [hind] at hmono
    exact hmono
  have hub : ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal |quantFn n (x j) - x j| ∂ν)
      ≤ ENNReal.ofReal (1/(n:ℝ)) + (∫⁻ x, tailInd j n x ∂ν) := by
    intro n
    calc ∫⁻ x, ENNReal.ofReal |quantFn n (x j) - x j| ∂ν
        ≤ ∫⁻ x, (ENNReal.ofReal (1/(n:ℝ)) + tailInd j n x) ∂ν :=
          lintegral_mono (fun x => hpt n x)
      _ = (∫⁻ x, ENNReal.ofReal (1/(n:ℝ)) ∂ν)
          + (∫⁻ x, tailInd j n x ∂ν) :=
          lintegral_add_left measurable_const _
      _ = ENNReal.ofReal (1/(n:ℝ)) + (∫⁻ x, tailInd j n x ∂ν) := by
          rw [lintegral_const, measure_univ, mul_one]
  have hu : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n:ℝ))
      + (∫⁻ x, tailInd j n x ∂ν)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/((n:ℝ)))) atTop (𝓝 0) := by
      have hr : Tendsto (fun n : ℕ => 1/((n:ℝ))) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have hc := ENNReal.continuous_ofReal.tendsto 0
      have hcomp := hc.comp hr
      rw [ENNReal.ofReal_zero] at hcomp
      exact hcomp
    have h2 := tail_tendsto_zero ν j hmom
    have hsum := h1.add h2
    simpa using hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hu (fun n => zero_le) hub

end Quant

section Pushforward

variable {d : ℕ}

/-- Coordinatewise quantization map (Section 7: `Z^{(n)}`). -/
@[expose] public noncomputable def quantVec (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => quantFn n (x j))

/-- The quantization map is measurable. -/
public theorem measurable_quantVec (n : ℕ) : Measurable (quantVec (d := d) n) := by
  have h : Measurable (fun x : EuclideanSpace ℝ (Fin d) => fun j => quantFn n (x j)) :=
    Measurable.of_eval fun j => (measurable_quantFn n).comp (measurable_coord j)
  have ho : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    WithLp.measurable_toLp 2 (Fin d → ℝ)
  exact ho.comp h

/-- Applying the quantization map acts coordinatewise. -/
private theorem quantVec_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    quantVec n x j = quantFn n (x j) := rfl

/-- The range of the quantization map is finite. -/
public theorem quantVec_range_finite (n : ℕ) :
    (Set.range (quantVec (d := d) n)).Finite := by
  classical
  have h1 : (Set.range (quantFn n)).Finite := quantFn_range_finite n
  haveI : Finite ↥(Set.range (quantFn n)) := h1
  haveI : Fintype ↥(Set.range (quantFn n)) := Fintype.ofFinite _
  apply Finite.of_injective (f := fun y : ↥(Set.range (quantVec (d := d) n)) =>
    (fun j => (⟨y.val j, by
      obtain ⟨x, hx⟩ := y.property
      have h2 : y.val j = quantFn n (x j) := by rw [← hx]; rfl
      rw [h2]
      exact ⟨x j, rfl⟩⟩ : ↥(Set.range (quantFn n)))))
  intro a b hab
  apply Subtype.ext
  have hfun : ∀ j : Fin d, a.val j = b.val j := by
    intro j
    have hj := congrFun hab j
    exact congrArg Subtype.val hj
  exact PiLp.ext hfun

/-- Quantized law `ν_n` (Section 7). -/
@[expose] public noncomputable def quantLaw (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ν.map (quantVec n)

/-- Quantized laws are probability laws. -/
public instance quantLaw_prob (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (quantLaw n ν) := ⟨by
  simp only [quantLaw, Measure.map_apply (measurable_quantVec n) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]⟩

/-- Quantized laws have finite support. -/
public theorem quantLaw_finite_support (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin d)), (quantLaw n ν) (↑s)ᶜ = 0 := by
  classical
  have hfin := quantVec_range_finite (d := d) n
  refine ⟨hfin.toFinset, ?_⟩
  have hsub : Set.range (quantVec (d := d) n) ⊆ ↑hfin.toFinset :=
    fun y hy => Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hy)
  have hmeas : MeasurableSet (↑hfin.toFinset : Set (EuclideanSpace ℝ (Fin d)))ᶜ :=
    ((Finset.finite_toSet _).measurableSet).compl
  rw [quantLaw, Measure.map_apply (measurable_quantVec n) hmeas]
  have hempty : (quantVec (d := d) n) ⁻¹' (↑hfin.toFinset : Set _)ᶜ = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact hx (hsub ⟨x, rfl⟩)
  rw [hempty, measure_empty]

/-- Finite-support probability laws are atomic laws (bridge to `oneStep`). -/
public theorem atomic_of_finite_support (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (s : Finset (EuclideanSpace ℝ (Fin d)))
    (hsupp : μ (↑s)ᶜ = 0) :
    ∃ (N : ℕ) (p : Fin N → ℝ) (Z : Fin N → EuclideanSpace ℝ (Fin d)),
      (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧ atomMeas (wgt p) Z = μ := by
  classical
  set s' : Finset (EuclideanSpace ℝ (Fin d)) := s.filter (fun z => μ {z} ≠ 0) with hs'def
  have hsub : s' ⊆ s := Finset.filter_subset _ _
  have hmeas_coe (t : Finset (EuclideanSpace ℝ (Fin d))) :
      MeasurableSet (t : Set (EuclideanSpace ℝ (Fin d))) :=
    (Finset.finite_toSet t).measurableSet
  have hdisj_single : ∀ a b : EuclideanSpace ℝ (Fin d), a ≠ b →
      Disjoint ({a} : Set _) {b} := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_singleton_iff] at hx1 hx2
    exact hab (hx1.symm.trans hx2)
  have hsum_coe : ∀ t : Finset (EuclideanSpace ℝ (Fin d)),
      μ ↑t = ∑ z ∈ t, μ {z} := by
    intro t
    have hunion : (↑t : Set _) = ⋃ z ∈ t, ({z} : Set _) := by
      ext x
      simp only [Finset.mem_coe, Set.mem_iUnion, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz
    rw [hunion]
    exact measure_biUnion_finset
      (fun a _ b _ hab => hdisj_single a b hab)
      (fun b _ => measurableSet_singleton b)
  have hμs : μ ↑s = 1 := by
    have h := measure_add_measure_compl (μ := μ) (hmeas_coe s)
    rw [hsupp, measure_univ, add_zero] at h
    exact h
  have hμs' : μ ↑s' = 1 := by
    have hsub2 : ∑ z ∈ s', μ {z} = ∑ z ∈ s, μ {z} := by
      apply Finset.sum_subset hsub
      intro z hzs hnmem
      have hnot : ¬ (μ {z} ≠ 0) := by
        intro hne
        apply hnmem
        rw [hs'def]
        exact Finset.mem_filter.mpr ⟨hzs, hne⟩
      exact not_not.mp hnot
    calc μ ↑s' = ∑ z ∈ s', μ {z} := hsum_coe s'
      _ = ∑ z ∈ s, μ {z} := hsub2
      _ = μ ↑s := (hsum_coe s).symm
      _ = 1 := hμs
  have hsupp' : μ (↑s')ᶜ = 0 := by
    have hfin : μ ↑s' ≠ ∞ := by rw [hμs']; exact ENNReal.one_lt_top.ne
    rw [measure_compl (hmeas_coe s') hfin, hμs', measure_univ]
    simp
  set N : ℕ := s'.card with hNdef
  set e : ↥(↑s' : Set (EuclideanSpace ℝ (Fin d))) ≃ Fin N := s'.equivFin with hedef
  set Z : Fin N → EuclideanSpace ℝ (Fin d) := fun i => (e.symm i).val with hZdef
  set p : Fin N → ℝ := fun i => (μ {Z i}).toReal with hpdef
  have hZmem : ∀ i, Z i ∈ s' := fun i => Finset.mem_coe.mp (e.symm i).property
  have hne : ∀ i, μ {Z i} ≠ 0 := by
    intro i
    have h := hZmem i
    rw [hs'def, Finset.mem_filter] at h
    exact h.2
  have hne_top : ∀ i, μ {Z i} ≠ ∞ := fun i =>
    ne_top_of_le_ne_top (by rw [measure_univ]; exact ENNReal.one_lt_top.ne)
      (measure_mono (Set.subset_univ _))
  have hpos : ∀ i, 0 < p i := fun i => ENNReal.toReal_pos (hne i) (hne_top i)
  have hwgt : ∀ i, wgt p i = μ {Z i} := fun i => ENNReal.ofReal_toReal (hne_top i)
  have hZinj : Function.Injective Z := by
    intro a b hab
    have hsub2 : e.symm a = e.symm b := Subtype.ext hab
    exact e.symm.injective hsub2
  have hZsurj : ∀ z ∈ s', ∃ i, Z i = z := by
    intro z hz
    refine ⟨e ⟨z, Finset.mem_coe.mpr hz⟩, ?_⟩
    show (e.symm (e ⟨z, Finset.mem_coe.mpr hz⟩)).val = z
    rw [Equiv.symm_apply_apply]
  have hre : ∑ i, μ {Z i} = ∑ z ∈ s', μ {z} := by
    apply Finset.sum_bij (fun i _ => Z i)
    · intro i _
      exact hZmem i
    · intro a₁ _ a₂ _ h
      exact hZinj h
    · intro z hz
      obtain ⟨i, rfl⟩ := hZsurj z hz
      exact ⟨i, Finset.mem_univ i, rfl⟩
    · intro i _
      rfl
  have hsum : ∑ i, p i = 1 := by
    have h1 : ∑ i, p i = (∑ i, μ {Z i}).toReal := by
      rw [ENNReal.toReal_sum (fun i _ => hne_top i)]
    rw [h1, hre, ← hsum_coe s', hμs', ENNReal.toReal_one]
  have hcore : ∀ w : Fin N → ℝ≥0∞, (∀ i, w i = μ {Z i}) → atomMeas w Z = μ := by
    intro w hw
    apply Measure.ext
    intro s0 hs0
    have happly : ∀ t : Finset (Fin N),
        (∑ i ∈ t, w i • Measure.dirac (Z i)) s0 = ∑ i ∈ t, (w i • Measure.dirac (Z i)) s0 := by
      intro t
      induction t using Finset.induction with
      | empty => simp
      | insert b t hb ih =>
        rw [Finset.sum_insert hb, Finset.sum_insert hb, Measure.add_apply, ih]
    have hterm : ∀ (a : ℝ≥0∞) (z : EuclideanSpace ℝ (Fin d)),
        (a • Measure.dirac z) s0 = (if z ∈ s0 then a else 0) := by
      intro a z
      rw [Measure.smul_apply, Measure.dirac_apply]
      split_ifs with hz
      · rw [Set.indicator_of_mem hz]
        simp [smul_eq_mul]
      · rw [Set.indicator_of_notMem hz]
        simp [smul_eq_mul]
    have hLHS : (atomMeas w Z) s0
        = ∑ i ∈ Finset.univ.filter (fun i => Z i ∈ s0), μ {Z i} := by
      have h0 : (atomMeas w Z) s0 = ∑ i, (w i • Measure.dirac (Z i)) s0 := by
        show ((∑ i, w i • Measure.dirac (Z i)) : Measure _) s0 = _
        exact happly Finset.univ
      calc (atomMeas w Z) s0 = ∑ i, (w i • Measure.dirac (Z i)) s0 := h0
        _ = ∑ i, (if Z i ∈ s0 then w i else 0) :=
          Finset.sum_congr rfl (fun i _ => hterm _ _)
        _ = ∑ i ∈ Finset.univ.filter (fun i => Z i ∈ s0), w i :=
          (Finset.sum_filter _ _).symm
        _ = ∑ i ∈ Finset.univ.filter (fun i => Z i ∈ s0), μ {Z i} :=
          Finset.sum_congr rfl (fun i _ => hw i)
    have hRHS : μ s0 = ∑ z ∈ s'.filter (fun z => z ∈ s0), μ {z} := by
      have hunion : s0 ∩ ↑s' ∪ s0 \ ↑s' = s0 := Set.inter_union_sdiff s0 ↑s'
      have hdisj : Disjoint (s0 ∩ ↑s') (s0 \ ↑s') := by
        rw [Set.disjoint_left]
        rintro x ⟨_, hx2⟩ ⟨_, hx3⟩
        exact hx3 hx2
      have hsub2 : s0 \ ↑s' ⊆ (↑s')ᶜ := fun x hx => hx.2
      have hnull : μ (s0 \ ↑s') = 0 :=
        le_antisymm (by rw [← hsupp']; exact measure_mono hsub2) zero_le
      have hinter : μ (s0 ∩ ↑s')
          = ∑ z ∈ s'.filter (fun z => z ∈ s0), μ {z} := by
        have hunion2 : s0 ∩ ↑s'
            = ⋃ z ∈ s'.filter (fun z => z ∈ s0), ({z} : Set _) := by
          ext x
          simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_iUnion,
            Finset.mem_filter, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨x, ⟨h2, h1⟩, rfl⟩
          · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
            exact ⟨hz2, hz1⟩
        rw [hunion2]
        exact measure_biUnion_finset
          (fun a _ b _ hab => hdisj_single a b hab)
          (fun b _ => measurableSet_singleton b)
      conv_lhs => rw [← hunion]
      rw [measure_union hdisj (hs0.diff (hmeas_coe s')), hinter, hnull, add_zero]
    rw [hLHS, hRHS]
    apply Finset.sum_bij (fun i _ => Z i)
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨hZmem i, hi.2⟩
    · intro a₁ _ a₂ _ h
      exact hZinj h
    · intro z hz
      rw [Finset.mem_filter] at hz
      obtain ⟨i, rfl⟩ := hZsurj z hz.1
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hz.2⟩, rfl⟩
    · intro i _
      rfl
  exact ⟨N, p, Z, hpos, hsum, hcore _ hwgt⟩

end Pushforward

section GapConv

variable {d : ℕ}

/-- Two-sided `ℝ≥0∞` squeeze against an error tending to zero. -/
private theorem tendsto_of_le_add_both {a e : ℕ → ℝ≥0∞} {b : ℝ≥0∞}
    (hup : ∀ n, a n ≤ b + e n) (hlo : ∀ n, b ≤ a n + e n)
    (he : Tendsto e atTop (𝓝 0)) : Tendsto a atTop (𝓝 b) := by
  have hev1 : ∀ᶠ n in atTop, e n < 1 :=
    (tendsto_order.1 he).2 1 zero_lt_one
  apply tendsto_order.2
  constructor
  · intro u hub
    by_cases hb : b = ∞
    · subst hb
      filter_upwards [hev1] with n hn
      have han : a n = ∞ := by
        by_contra hne
        have hfin : a n + e n < ∞ :=
          ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hne,
            lt_trans hn ENNReal.one_lt_top⟩
        exact lt_irrefl ∞ (lt_of_le_of_lt (hlo n) hfin)
      rw [han]
      exact hub
    · have hδ : (0 : ℝ≥0∞) < b - u := by
        apply lt_of_le_of_ne zero_le
        intro h0
        have hle : b ≤ u := tsub_eq_zero_iff_le.mp h0.symm
        exact absurd hle (not_le.mpr hub)
      have hev : ∀ᶠ n in atTop, e n < b - u := (tendsto_order.1 he).2 _ hδ
      filter_upwards [hev] with n hn
      by_contra hcon
      push Not at hcon
      have hune : u ≠ ∞ := ne_top_of_le_ne_top hb hub.le
      have h1 : a n + e n ≤ u + e n := add_le_add_left hcon _
      have h2 : u + e n < u + (b - u) := ENNReal.add_lt_add_left hune hn
      rw [add_tsub_cancel_of_le hub.le] at h2
      exact lt_irrefl b (lt_of_le_of_lt (le_trans (hlo n) h1) h2)
  · intro v hbv
    by_cases hv : v = ∞
    · subst hv
      have hb : b < ∞ := hbv
      filter_upwards [hev1] with n hn
      exact lt_of_le_of_lt (hup n)
        (ENNReal.add_lt_top.mpr ⟨hb, lt_trans hn ENNReal.one_lt_top⟩)
    · have hδ : (0 : ℝ≥0∞) < v - b := by
        apply lt_of_le_of_ne zero_le
        intro h0
        have hle : v ≤ b := tsub_eq_zero_iff_le.mp h0.symm
        exact absurd hle (not_le.mpr hbv)
      have hev : ∀ᶠ n in atTop, e n < v - b := (tendsto_order.1 he).2 _ hδ
      filter_upwards [hev] with n hn
      have hbne : b ≠ ∞ := ne_top_of_le_ne_top hv hbv.le
      have h2 : b + e n < b + (v - b) := ENNReal.add_lt_add_left hbne hn
      rw [add_tsub_cancel_of_le hbv.le] at h2
      exact lt_of_le_of_lt (hup n) h2

/-- `ofReal` form of the gap integrand. -/
private theorem ofReal_abs_eq_nnnorm (x y : ℝ) :
    ENNReal.ofReal |x - y| = ((‖x - y‖₊ : ℝ≥0) : ℝ≥0∞) := by
  have h : |x - y| = ((((‖x - y‖₊ : ℝ≥0))) : ℝ) := by
    rw [coe_nnnorm, Real.norm_eq_abs]
  rw [h, ENNReal.ofReal_coe_nnreal]

/-- The gap as an `ofReal` integral. -/
private theorem gap_eq_ofReal (μ : Measure (EuclideanSpace ℝ (Fin d))) (j : Fin d) :
    gap j μ = ∫⁻ p, ENNReal.ofReal |p.1 j - p.2 j| ∂(μ.prod μ) := by
  unfold gap
  apply lintegral_congr_ae
  filter_upwards with p
  exact (ofReal_abs_eq_nnnorm _ _).symm

/-- Change of variables for the quantized gap. -/
private theorem gap_quant_chg (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (j : Fin d) (n : ℕ) :
    gap j (quantLaw n ν)
      = ∫⁻ p, ENNReal.ofReal |quantFn n (p.1 j) - quantFn n (p.2 j)| ∂(ν.prod ν) := by
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal |p.1 j - p.2 j|) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_coord j).comp measurable_fst).sub
        ((measurable_coord j).comp measurable_snd)).abs
  have hmap : Measurable (Prod.map (quantVec n) (quantVec n) :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → _) :=
    (measurable_quantVec n).prodMap (measurable_quantVec n)
  rw [gap_eq_ofReal, quantLaw,
    map_prod_map _ _ (measurable_quantVec n) (measurable_quantVec n),
    lintegral_map hmeas hmap]
  apply lintegral_congr_ae
  filter_upwards with p
  simp only [Prod.map_fst, Prod.map_snd, quantVec_apply]

/-- Integrating a first-coordinate function over a product of probability laws. -/
private theorem lintegral_prod_fst (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ p, F p.1 ∂(ν.prod ν) = ∫⁻ x, F x ∂ν := by
  have hF' : AEMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      F p.1) (ν.prod ν) :=
    (hF.comp measurable_fst).aemeasurable
  rw [lintegral_prod _ hF']
  apply lintegral_congr_ae
  filter_upwards with x
  have hconst : (fun y : EuclideanSpace ℝ (Fin d) => F (x, y).1) = fun _ => F x := rfl
  rw [hconst, lintegral_const, measure_univ, mul_one]

/-- Integrating a second-coordinate function over a product of probability laws. -/
private theorem lintegral_prod_snd (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ p, F p.2 ∂(ν.prod ν) = ∫⁻ x, F x ∂ν := by
  have hF' : AEMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      F p.2) (ν.prod ν) :=
    (hF.comp measurable_snd).aemeasurable
  rw [lintegral_prod _ hF']
  have hinner : ∀ x : EuclideanSpace ℝ (Fin d),
      (∫⁻ y, F (x, y).2 ∂ν) = ∫⁻ y, F y ∂ν := by
    intro x
    apply lintegral_congr_ae
    filter_upwards with y
    rfl
  simp only [hinner]
  rw [lintegral_const, measure_univ, mul_one]

/-- Uniform moment bound for the quantization (Section 7: `E|Z^{(n,j)}| ≤ E|Z^{(j)}|+1`). -/
public theorem quant_moment_bound (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (j : Fin d) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal |quantFn n (x j)| ∂ν
      ≤ (∫⁻ x, ENNReal.ofReal |x j| ∂ν) + 1 := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal |quantFn n (x j)| ≤ ENNReal.ofReal |x j| + 1 := by
    intro x
    have hb := quantFn_abs_le n (x j)
    have hmono := ENNReal.ofReal_le_ofReal hb
    rw [ENNReal.ofReal_add (abs_nonneg _) zero_le_one, ENNReal.ofReal_one] at hmono
    exact hmono
  calc ∫⁻ x, ENNReal.ofReal |quantFn n (x j)| ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal |x j| + 1) ∂ν := lintegral_mono (fun x => hpt x)
    _ = (∫⁻ x, ENNReal.ofReal |x j| ∂ν) + ∫⁻ _, (1 : ℝ≥0∞) ∂ν :=
        lintegral_add_left (ENNReal.measurable_ofReal.comp
          ((measurable_coord j).abs)) _
    _ = (∫⁻ x, ENNReal.ofReal |x j| ∂ν) + 1 := by
        rw [lintegral_const, measure_univ, mul_one]

/-- Gap convergence under quantization (HI-GAPCONV). -/
public theorem gap_quant_tendsto (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (j : Fin d)
    (hmom : ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞) :
    Tendsto (fun n => gap j (quantLaw n ν)) atTop (𝓝 (gap j ν)) := by
  set L : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ENNReal.ofReal |quantFn n (x j) - x j| ∂ν
    with hLdef
  have hL0 : Tendsto L atTop (𝓝 0) := quant_l1_tendsto ν j hmom
  have he : Tendsto (fun n => L n + L n) atTop (𝓝 0) := by
    simpa using hL0.add hL0
  have hH1meas : ∀ n : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal |quantFn n (p.1 j) - p.1 j|) := by
    intro n
    exact ENNReal.measurable_ofReal.comp
      (((measurable_quantFn n).comp ((measurable_coord j).comp measurable_fst)).sub
        ((measurable_coord j).comp measurable_fst)).abs
  have hH2meas : ∀ n : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal |quantFn n (p.2 j) - p.2 j|) := by
    intro n
    exact ENNReal.measurable_ofReal.comp
      (((measurable_quantFn n).comp ((measurable_coord j).comp measurable_snd)).sub
        ((measurable_coord j).comp measurable_snd)).abs
  have hH1 : ∀ n : ℕ, (∫⁻ p, ENNReal.ofReal |quantFn n (p.1 j) - p.1 j| ∂(ν.prod ν))
      = L n := by
    intro n
    have h := lintegral_prod_fst ν (fun x => ENNReal.ofReal |quantFn n (x j) - x j|)
      (ENNReal.measurable_ofReal.comp
        (((measurable_quantFn n).comp (measurable_coord j)).sub
          (measurable_coord j)).abs)
    exact h
  have hH2 : ∀ n : ℕ, (∫⁻ p, ENNReal.ofReal |quantFn n (p.2 j) - p.2 j| ∂(ν.prod ν))
      = L n := by
    intro n
    have h := lintegral_prod_snd ν (fun x => ENNReal.ofReal |quantFn n (x j) - x j|)
      (ENNReal.measurable_ofReal.comp
        (((measurable_quantFn n).comp (measurable_coord j)).sub
          (measurable_coord j)).abs)
    exact h
  have hint : ∀ (n : ℕ) (B : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      Measurable B →
      ∫⁻ p, (B p + (ENNReal.ofReal |quantFn n (p.1 j) - p.1 j|
        + ENNReal.ofReal |quantFn n (p.2 j) - p.2 j|)) ∂(ν.prod ν)
        = (∫⁻ p, B p ∂(ν.prod ν)) + (L n + L n) := by
    intro n B hB
    rw [lintegral_add_left hB _, lintegral_add_left (hH1meas n) _, hH1 n, hH2 n]
  have hR : ∀ n : ℕ, ∀ a b c e : ℝ,
      |a - b| ≤ |c - e| + (|a - c| + |b - e|) := by
    intro n a b c e
    have h1 : |(|a - b| - |c - e|)| ≤ |(a - b) - (c - e)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    have h2 : |(a - b) - (c - e)| ≤ |a - c| + |b - e| := by
      have heq : (a - b) - (c - e) = (a - c) - (b - e) := by ring
      rw [heq]
      exact abs_sub _ _
    have h3 := le_trans (le_abs_self _) (le_trans h1 h2)
    linarith
  have hpt : ∀ n : ℕ, ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal |quantFn n (p.1 j) - quantFn n (p.2 j)|
        ≤ ENNReal.ofReal |p.1 j - p.2 j|
          + (ENNReal.ofReal |quantFn n (p.1 j) - p.1 j|
            + ENNReal.ofReal |quantFn n (p.2 j) - p.2 j|) := by
    intro n p
    have hb := hR n (quantFn n (p.1 j)) (quantFn n (p.2 j)) (p.1 j) (p.2 j)
    have hmono := ENNReal.ofReal_le_ofReal hb
    rw [ENNReal.ofReal_add (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _)),
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at hmono
    exact hmono
  have hpt2 : ∀ n : ℕ, ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal |p.1 j - p.2 j|
        ≤ ENNReal.ofReal |quantFn n (p.1 j) - quantFn n (p.2 j)|
          + (ENNReal.ofReal |quantFn n (p.1 j) - p.1 j|
            + ENNReal.ofReal |quantFn n (p.2 j) - p.2 j|) := by
    intro n p
    have hb := hR n (p.1 j) (p.2 j) (quantFn n (p.1 j)) (quantFn n (p.2 j))
    have habs : |quantFn n (p.1 j) - p.1 j| = |p.1 j - quantFn n (p.1 j)| := by
      rw [abs_sub_comm]
    have habs2 : |quantFn n (p.2 j) - p.2 j| = |p.2 j - quantFn n (p.2 j)| := by
      rw [abs_sub_comm]
    rw [habs, habs2] at ⊢
    have hmono := ENNReal.ofReal_le_ofReal hb
    rw [ENNReal.ofReal_add (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _)),
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at hmono
    exact hmono
  have hGmeas : Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal |p.1 j - p.2 j|) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_coord j).comp measurable_fst).sub
        ((measurable_coord j).comp measurable_snd)).abs
  have hFmeas : ∀ n : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal |quantFn n (p.1 j) - quantFn n (p.2 j)|) := by
    intro n
    have hA : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        quantFn n (p.1 j)) :=
      (measurable_quantFn n).comp ((measurable_coord j).comp measurable_fst)
    have hB : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        quantFn n (p.2 j)) :=
      (measurable_quantFn n).comp ((measurable_coord j).comp measurable_snd)
    exact ENNReal.measurable_ofReal.comp (hA.sub hB).abs
  apply tendsto_of_le_add_both _ _ he
  · intro n
    rw [gap_quant_chg ν j n, gap_eq_ofReal]
    calc ∫⁻ p, ENNReal.ofReal |quantFn n (p.1 j) - quantFn n (p.2 j)| ∂(ν.prod ν)
        ≤ ∫⁻ p, (ENNReal.ofReal |p.1 j - p.2 j|
            + (ENNReal.ofReal |quantFn n (p.1 j) - p.1 j|
              + ENNReal.ofReal |quantFn n (p.2 j) - p.2 j|)) ∂(ν.prod ν) :=
          lintegral_mono (fun p => hpt n p)
      _ = (∫⁻ p, ENNReal.ofReal |p.1 j - p.2 j| ∂(ν.prod ν)) + (L n + L n) :=
          hint n _ hGmeas
  · intro n
    rw [gap_quant_chg ν j n, gap_eq_ofReal]
    calc ∫⁻ p, ENNReal.ofReal |p.1 j - p.2 j| ∂(ν.prod ν)
        ≤ ∫⁻ p, (ENNReal.ofReal |quantFn n (p.1 j) - quantFn n (p.2 j)|
            + (ENNReal.ofReal |quantFn n (p.1 j) - p.1 j|
              + ENNReal.ofReal |quantFn n (p.2 j) - p.2 j|)) ∂(ν.prod ν) :=
          lintegral_mono (fun p => hpt2 n p)
      _ = (∫⁻ p, ENNReal.ofReal |quantFn n (p.1 j) - quantFn n (p.2 j)| ∂(ν.prod ν))
          + (L n + L n) := hint n _ (hFmeas n)

end GapConv

section DetMono

variable {k : ℕ}

/-- Crude determinant bound by row sums. -/
private theorem abs_det_le_factorial_mul_prod_rowsum {ι : Type*} [DecidableEq ι] [Fintype ι]
    (M : Matrix ι ι ℝ) :
    |M.det| ≤ (Fintype.card ι)! * ∏ r, ∑ c, |M r c| := by
  rw [Matrix.det_apply]
  have htri : |∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ • ∏ i, M (σ i) i)|
      ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, M (σ i) i| :=
    abs_sum_le_sum_abs _ _
  refine le_trans htri ?_
  have hsign : ∀ s : ℤˣ, ∀ x : ℝ, |s • x| = |x| := by
    intro s x
    rcases Int.units_eq_one_or s with h | h
    · rw [h, one_smul]
    · rw [h]
      simp
  have hmono : ∀ σ : Equiv.Perm ι,
      |Equiv.Perm.sign σ • ∏ i, M (σ i) i| ≤ ∏ r, ∑ c, |M r c| := by
    intro σ
    rw [hsign, abs_prod]
    have h1 : ∀ i : ι, |M (σ i) i| ≤ ∑ c, |M (σ i) c| := fun i =>
      Finset.single_le_sum (fun c _ => abs_nonneg (M (σ i) c)) (Finset.mem_univ i)
    have h2 : (∏ i, |M (σ i) i|) ≤ ∏ i, ∑ c, |M (σ i) c| := by
      have hgen : ∀ s : Finset ι, (∏ i ∈ s, |M (σ i) i|) ≤ ∏ i ∈ s, ∑ c, |M (σ i) c| := by
        intro s
        induction s using Finset.induction with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.prod_insert ha]
          exact mul_le_mul (h1 a) ih
            (Finset.prod_nonneg (fun i _ => abs_nonneg _))
            (Finset.sum_nonneg (fun c _ => abs_nonneg _))
      exact hgen Finset.univ
    have h3 : (∏ i, ∑ c, |M (σ i) c|) = ∏ r, ∑ c, |M r c| :=
      Equiv.prod_comp σ (fun r => ∑ c, |M r c|)
    rw [h3] at h2
    exact h2
  calc ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, M (σ i) i|
      ≤ ∑ _σ : Equiv.Perm ι, (∏ r, ∑ c, |M r c|) :=
        Finset.sum_le_sum (fun σ _ => hmono σ)
    _ = (Fintype.card ι)! * ∏ r, ∑ c, |M r c| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- Interpolating matrices between true and quantized rows. -/
private noncomputable def teleMat (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k))
    (j : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  Matrix.of (fun r c => if r.val < j then Fin.cases (1:ℝ) (fun t => quantVec n (Z r) t) c
    else Fin.cases (1:ℝ) (fun t => (Z r) t) c)

/-- Telescope base: all rows true. -/
private theorem teleMat_zero (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k)) :
    teleMat n Z 0 = Matrix.of (fun r c => Fin.cases (1:ℝ) (fun t => (Z r) t) c) := by
  funext r c
  simp only [teleMat, Matrix.of_apply]
  split_ifs with h
  · exact absurd h (Nat.not_lt_zero _)
  · rfl

/-- Telescope top: all rows quantized. -/
private theorem teleMat_top (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k)) :
    teleMat n Z (k+1)
      = Matrix.of (fun r c => Fin.cases (1:ℝ) (fun t => quantVec n (Z r) t) c) := by
  funext r c
  simp only [teleMat, Matrix.of_apply]
  split_ifs with h
  · rfl
  · exact absurd (Fin.is_lt r) h

/-- Telescope step: only row `j` changes. -/
private theorem teleMat_succ (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k))
    (j : ℕ) (hj : j < k+1) :
    teleMat n Z (j+1)
      = (teleMat n Z j).updateRow ⟨j, hj⟩
        (fun c => Fin.cases (1:ℝ) (fun t => quantVec n (Z ⟨j,hj⟩) t) c) := by
  funext r c
  simp only [teleMat, Matrix.of_apply, Matrix.updateRow_apply]
  by_cases hr : r = ⟨j, hj⟩
  · subst hr
    simp only [Nat.lt_succ_self j, ite_true]
  · have hne : r.val ≠ j := fun h => hr (Fin.ext h)
    simp only [hr, ite_false]
    by_cases h1 : r.val < j
    · have h2 : r.val < j + 1 := Nat.lt_succ_of_lt h1
      simp only [h1, h2, ite_true]
    · have h2 : ¬ r.val < j + 1 := by omega
      simp only [h1, h2, ite_false]

/-- Telescope determinant step via row linearity. -/
private theorem teleMat_det_step (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k))
    (j : ℕ) (hj : j < k+1) :
    (teleMat n Z (j+1)).det - (teleMat n Z j).det
    = ((teleMat n Z j).updateRow ⟨j,hj⟩
        (fun c => Fin.cases (1:ℝ) (fun t => quantVec n (Z ⟨j,hj⟩) t) c
          - Fin.cases (1:ℝ) (fun t => (Z ⟨j,hj⟩) t) c)).det := by
  have hmat := teleMat_succ n Z j hj
  set Wrow : Fin (k+1) → ℝ :=
    fun c => Fin.cases (1:ℝ) (fun t => quantVec n (Z ⟨j,hj⟩) t) c with hWdef
  set Vrow : Fin (k+1) → ℝ :=
    fun c => Fin.cases (1:ℝ) (fun t => (Z ⟨j,hj⟩) t) c with hVdef
  set Urow : Fin (k+1) → ℝ := fun c => Wrow c - Vrow c with hUdef
  have hadd : Urow + Vrow = Wrow := by
    funext c
    simp only [hUdef, Pi.add_apply, sub_add_cancel]
  have hrow : Vrow = (teleMat n Z j) ⟨j,hj⟩ := by
    funext c
    simp only [hVdef, teleMat, Matrix.of_apply]
    split_ifs with h
    · exact absurd h (Nat.lt_irrefl j)
    · rfl
  have hself : ((teleMat n Z j).updateRow ⟨j,hj⟩ Vrow) = teleMat n Z j := by
    rw [hrow]
    exact Matrix.updateRow_eq_self _ _
  rw [hmat, ← hadd, Matrix.det_updateRow_add, hself, add_sub_cancel_right]

/-- Row marginal of a product of probability laws. -/
private theorem lintegral_row (ν : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν] (r : Fin (k+1)) (H : EuclideanSpace ℝ (Fin k) → ℝ≥0∞)
    (hH : Measurable H) :
    ∫⁻ Z, H (Z r) ∂(Measure.pi (fun _ : Fin (k+1) => ν)) = ∫⁻ x, H x ∂ν := by
  have hmap : (Measure.pi (fun _ : Fin (k+1) => ν)).map (Function.eval r) = ν := by
    have h := pi_map_eval (fun _ : Fin (k+1) => ν) r
    rw [h]
    simp [measure_univ]
  have hg : Measurable (Function.eval r :
      (Fin (k+1) → EuclideanSpace ℝ (Fin k)) → EuclideanSpace ℝ (Fin k)) :=
    measurable_pi_apply r
  conv_rhs => rw [← hmap]
  rw [← lintegral_map hH hg]

/-- Difference-row factor (ENNReal). -/
private noncomputable def diffRowSum (n : ℕ) (x : EuclideanSpace ℝ (Fin k)) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal |quantVec n x j - x j|

private theorem measurable_diffRowSum (n : ℕ) : Measurable (diffRowSum (k := k) n) := by
  unfold diffRowSum
  apply Finset.measurable_sum
  intro j _
  exact ENNReal.measurable_ofReal.comp
    (((measurable_quantFn n).comp (measurable_coord j)).sub (measurable_coord j)).abs

/-- Uniform row-sum factor (ENNReal). -/
private noncomputable def rowSumBnd (n : ℕ) (x : EuclideanSpace ℝ (Fin k)) : ℝ≥0∞ :=
  1 + ∑ j, (ENNReal.ofReal |x j| + ENNReal.ofReal |quantFn n (x j)|)

private theorem measurable_rowSumBnd (n : ℕ) : Measurable (rowSumBnd (k := k) n) := by
  unfold rowSumBnd
  exact Measurable.add measurable_const (Finset.measurable_sum _ (fun j _ =>
    Measurable.add
      (ENNReal.measurable_ofReal.comp (measurable_coord j).abs)
      (ENNReal.measurable_ofReal.comp
        (((measurable_quantFn n).comp (measurable_coord j)).abs))))

/-- Rowsum of a `(1; g)` row in ofReal form. -/
private theorem ofReal_rowsum_split (F : Fin (k+1) → ℝ) (g : Fin k → ℝ)
    (h0 : F 0 = 1) (hs : ∀ j, F j.succ = g j) :
    ENNReal.ofReal (∑ c, |F c|) = 1 + ∑ j, ENNReal.ofReal |g j| := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => abs_nonneg _), Fin.sum_univ_succ]
  have hF0 : ENNReal.ofReal |F 0| = 1 := by rw [h0, abs_one, ENNReal.ofReal_one]
  have hFs : (∑ i : Fin k, ENNReal.ofReal |F i.succ|) = ∑ j, ENNReal.ofReal |g j| :=
    Finset.sum_congr rfl (fun j _ => by rw [hs j])
  rw [hF0, hFs]

/-- Rowsum of a `(0; g)` row in ofReal form. -/
private theorem ofReal_rowsum_split0 (F : Fin (k+1) → ℝ) (g : Fin k → ℝ)
    (h0 : F 0 = 0) (hs : ∀ j, F j.succ = g j) :
    ENNReal.ofReal (∑ c, |F c|) = ∑ j, ENNReal.ofReal |g j| := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => abs_nonneg _), Fin.sum_univ_succ]
  have hF0 : ENNReal.ofReal |F 0| = 0 := by rw [h0, abs_zero, ENNReal.ofReal_zero]
  have hFs : (∑ i : Fin k, ENNReal.ofReal |F i.succ|) = ∑ j, ENNReal.ofReal |g j| :=
    Finset.sum_congr rfl (fun j _ => by rw [hs j])
  rw [hF0, hFs, zero_add]

/-- Pointwise bound for non-diff rows. -/
private theorem rowsum_other_le (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k))
    (j : ℕ) (hj : j < k+1) (r' : Fin (k+1)) (hr' : r' ≠ ⟨j, hj⟩)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hD : ∀ c, D r' c = teleMat n Z j r' c) :
    ENNReal.ofReal (∑ c, |D r' c|) ≤ rowSumBnd n (Z r') := by
  by_cases hc : r'.val < j
  · have hW : ∀ c, D r' c
        = Fin.cases (1:ℝ) (fun t => quantVec n (Z r') t) c := by
      intro c
      rw [hD c]
      simp only [teleMat, Matrix.of_apply, hc, ite_true]
    have h0 : D r' 0 = 1 := by rw [hW 0, Fin.cases_zero]
    have hs : ∀ t, D r' t.succ = quantVec n (Z r') t := by
      intro t
      rw [hW _]
      exact Fin.cases_succ t
    rw [ofReal_rowsum_split _ _ h0 hs]
    unfold rowSumBnd
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro t _
    exact le_add_of_nonneg_left zero_le
  · have hV : ∀ c, D r' c = Fin.cases (1:ℝ) (fun t => (Z r') t) c := by
      intro c
      rw [hD c]
      simp only [teleMat, Matrix.of_apply, hc, ite_false]
    have h0 : D r' 0 = 1 := by rw [hV 0, Fin.cases_zero]
    have hs : ∀ t, D r' t.succ = (Z r') t := by
      intro t
      rw [hV _]
      exact Fin.cases_succ t
    rw [ofReal_rowsum_split _ _ h0 hs]
    unfold rowSumBnd
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro t _
    exact le_add_of_nonneg_right zero_le

/-- Pointwise evaluation for the diff row. -/
private theorem rowsum_diff_eq (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k))
    (j : ℕ) (hj : j < k+1)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hD : ∀ c, D ⟨j,hj⟩ c
      = Fin.cases (1:ℝ) (fun t => quantVec n (Z ⟨j,hj⟩) t) c
        - Fin.cases (1:ℝ) (fun t => (Z ⟨j,hj⟩) t) c) :
    ENNReal.ofReal (∑ c, |D ⟨j,hj⟩ c|) = diffRowSum n (Z ⟨j,hj⟩) := by
  have h0 : D ⟨j,hj⟩ 0 = 0 := by
    rw [hD 0, Fin.cases_zero, Fin.cases_zero, sub_self]
  have hs : ∀ t, D ⟨j,hj⟩ t.succ = quantVec n (Z ⟨j,hj⟩) t - (Z ⟨j,hj⟩) t := by
    intro t
    rw [hD _, Fin.cases_succ, Fin.cases_succ]
  rw [ofReal_rowsum_split0 _ _ h0 hs]
  rfl

/-- Telescope determinants are measurable in the samples. -/
private theorem measurable_teleMat_det (n j : ℕ) : Measurable
    (fun Z : Fin (k+1) → EuclideanSpace ℝ (Fin k) => (teleMat n Z j).det) := by
  have hmat : Measurable (fun Z : Fin (k+1) → EuclideanSpace ℝ (Fin k) => teleMat n Z j) := by
    apply Measurable.of_eval
    intro r
    apply Measurable.of_eval
    intro c
    simp only [teleMat, Matrix.of_apply]
    by_cases hc : r.val < j
    · simp only [hc, ite_true]
      obtain rfl | ⟨t, rfl⟩ := Fin.eq_zero_or_eq_succ c
      · simp only [Fin.cases_zero]
        exact measurable_const
      · simp only [Fin.cases_succ]
        exact ((measurable_quantFn n).comp (measurable_coord t)).comp
          (measurable_pi_apply r)
    · simp only [hc, ite_false]
      obtain rfl | ⟨t, rfl⟩ := Fin.eq_zero_or_eq_succ c
      · simp only [Fin.cases_zero]
        exact measurable_const
      · simp only [Fin.cases_succ]
        exact (measurable_coord t).comp (measurable_pi_apply r)
  exact (Continuous.matrix_det continuous_id).measurable.comp hmat

/-- Difference row for the telescope step. -/
private noncomputable def stepRow (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k))
    (j : ℕ) (hj : j < k+1) : Fin (k+1) → ℝ :=
  fun c => Fin.cases (1:ℝ) (fun t => quantVec n (Z ⟨j,hj⟩) t) c
    - Fin.cases (1:ℝ) (fun t => (Z ⟨j,hj⟩) t) c

/-- Telescope step matrix. -/
private noncomputable def stepMat (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k))
    (j : ℕ) (hj : j < k+1) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  (teleMat n Z j).updateRow ⟨j,hj⟩ (stepRow n Z j hj)

/-- Row factor for the independence argument. -/
private noncomputable def stepFactor (n : ℕ) (j : ℕ) (hj : j < k+1)
    (r' : Fin (k+1)) (x : EuclideanSpace ℝ (Fin k)) : ℝ≥0∞ :=
  if r' = ⟨j, hj⟩ then diffRowSum n x else rowSumBnd n x

private theorem measurable_stepFactor (n : ℕ) (j : ℕ) (hj : j < k+1)
    (r' : Fin (k+1)) : Measurable (stepFactor (k := k) n j hj r') := by
  unfold stepFactor
  by_cases hr' : r' = ⟨j, hj⟩
  · simp only [hr', ite_true]
    exact measurable_diffRowSum n
  · simp only [hr', ite_false]
    exact measurable_rowSumBnd n

/-- Pointwise per-term bound by independent row factors. -/
private theorem term_ptwise (n : ℕ) (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k))
    (j : ℕ) (hj : j < k+1) :
    ENNReal.ofReal |(stepMat n Z j hj).det|
      ≤ ((k+1)! : ℝ≥0∞) * ∏ r', stepFactor n j hj r' (Z r') := by
  have hdet := abs_det_le_factorial_mul_prod_rowsum (stepMat n Z j hj)
  rw [Fintype.card_fin (k+1)] at hdet
  have hmono := ENNReal.ofReal_le_ofReal hdet
  have hprod_eq : ENNReal.ofReal (∏ r', ∑ c, |(stepMat n Z j hj) r' c|)
      = ∏ r', ENNReal.ofReal (∑ c, |(stepMat n Z j hj) r' c|) :=
    ENNReal.ofReal_prod_of_nonneg
      (fun r' _ => Finset.sum_nonneg (fun c _ => abs_nonneg _))
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), hprod_eq] at hmono
  have hprod : (∏ r', ENNReal.ofReal (∑ c, |(stepMat n Z j hj) r' c|))
      ≤ ∏ r', stepFactor n j hj r' (Z r') := by
    apply Finset.prod_le_prod
    intro r' _
    by_cases hr' : r' = ⟨j, hj⟩
    · subst hr'
      simp only [stepFactor, eq_self_iff_true, ite_true]
      have hD : ∀ c, stepMat n Z j hj ⟨j,hj⟩ c
          = Fin.cases (1:ℝ) (fun t => quantVec n (Z ⟨j,hj⟩) t) c
            - Fin.cases (1:ℝ) (fun t => (Z ⟨j,hj⟩) t) c := by
        intro c
        simp only [stepMat, stepRow, Matrix.updateRow_apply, eq_self_iff_true, ite_true]
      exact (rowsum_diff_eq n Z j hj _ hD).le
    · simp only [stepFactor, hr', ite_false]
      apply rowsum_other_le n Z j hj r' hr'
      intro c
      simp only [stepMat, Matrix.updateRow_apply, hr', ite_false]
  calc ENNReal.ofReal |(stepMat n Z j hj).det|
      ≤ ENNReal.ofReal ↑((k+1)!) * ∏ r', ENNReal.ofReal (∑ c, |(stepMat n Z j hj) r' c|) :=
        hmono
    _ = ((k+1)! : ℝ≥0∞) * ∏ r', ENNReal.ofReal (∑ c, |(stepMat n Z j hj) r' c|) := by
        rw [ENNReal.ofReal_natCast]
    _ ≤ ((k+1)! : ℝ≥0∞) * ∏ r', stepFactor n j hj r' (Z r') :=
        mul_le_mul_right hprod _

/-- Per-term convergence for one telescope step. -/
private theorem term_tendsto (ν : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin k, ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (j : ℕ) (hj : j < k+1) :
    Tendsto (fun n : ℕ => ∫⁻ Z, ENNReal.ofReal
        |(teleMat n Z (j+1)).det - (teleMat n Z j).det|
        ∂(Measure.pi (fun _ : Fin (k+1) => ν))) atTop (𝓝 0) := by
  have heq : (fun n : ℕ => ∫⁻ Z, ENNReal.ofReal
        |(teleMat n Z (j+1)).det - (teleMat n Z j).det|
        ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
      = (fun n : ℕ => ∫⁻ Z, ENNReal.ofReal |(stepMat n Z j hj).det|
        ∂(Measure.pi (fun _ : Fin (k+1) => ν))) := by
    funext n
    apply lintegral_congr_ae
    filter_upwards with Z
    exact congrArg (fun d => ENNReal.ofReal |d|) (teleMat_det_step n Z j hj)
  rw [heq]
  set F : ℝ≥0∞ := (((k+1)! : ℕ) : ℝ≥0∞) with hFdef
  have hFne : F ≠ ∞ := by rw [hFdef]; exact ENNReal.natCast_ne_top _
  set M : Fin k → ℝ≥0∞ := fun j => ∫⁻ x, ENNReal.ofReal |x j| ∂ν with hMdef
  have hMfin : ∀ j, M j < ∞ := by
    intro j
    have hcongr : (∫⁻ x, ENNReal.ofReal |x j| ∂ν)
        = ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards with x
      have h : |x j| = ((((‖x j‖₊ : ℝ≥0))) : ℝ) := by
        rw [coe_nnnorm, Real.norm_eq_abs]
      rw [h, ENNReal.ofReal_coe_nnreal]
    show M j < ∞
    rw [hMdef]
    show (∫⁻ x, ENNReal.ofReal |x j| ∂ν) < ∞
    rw [hcongr]
    exact lt_top_iff_ne_top.mpr (hmom j)
  set C : ℝ≥0∞ := 1 + ∑ j, (M j + (M j + 1)) with hCdef
  have hCfin : C < ∞ := by
    have h1 : ∀ j : Fin k, M j + (M j + 1) < ∞ := fun j =>
      ENNReal.add_lt_top.mpr ⟨hMfin j, ENNReal.add_lt_top.mpr ⟨hMfin j, ENNReal.one_lt_top⟩⟩
    have hsum : (∑ j, (M j + (M j + 1))) < ∞ := by
      have hgen : ∀ s : Finset (Fin k), (∑ j ∈ s, (M j + (M j + 1))) < ∞ := by
        intro s
        induction s using Finset.induction with
        | empty => simp [ENNReal.zero_lt_top]
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          exact ENNReal.add_lt_top.mpr ⟨h1 a, ih⟩
      exact hgen Finset.univ
    rw [hCdef]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hsum⟩
  have hCne : C ≠ ∞ := hCfin.ne
  have hCk : ∀ m : ℕ, C ^ m ≠ ∞ := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact ENNReal.one_lt_top.ne
    | succ m ih => rw [pow_succ]; exact ENNReal.mul_ne_top ih hCne
  have hdiff : ∀ n, ∫⁻ x, stepFactor n j hj ⟨j,hj⟩ x ∂ν
      = ∑ t, ∫⁻ x, ENNReal.ofReal |quantVec n x t - x t| ∂ν := by
    intro n
    have hif : (fun x => stepFactor n j hj ⟨j,hj⟩ x) = fun x => diffRowSum n x := by
      funext x
      simp only [stepFactor, eq_self_iff_true, ite_true]
    rw [hif]
    unfold diffRowSum
    exact lintegral_finsetSum _ (fun t _ => ENNReal.measurable_ofReal.comp
      (((measurable_quantFn n).comp (measurable_coord t)).sub (measurable_coord t)).abs)
  have hother : ∀ n, ∀ r' : Fin (k+1), r' ≠ ⟨j,hj⟩ →
      ∫⁻ x, stepFactor n j hj r' x ∂ν ≤ C := by
    intro n r' hr'
    have hif : (fun x => stepFactor n j hj r' x) = fun x => rowSumBnd n x := by
      funext x
      simp only [stepFactor, hr', ite_false]
    rw [hif]
    have hcomp : ∫⁻ x, rowSumBnd n x ∂ν
        = 1 + ∑ t, ((∫⁻ x, ENNReal.ofReal |x t| ∂ν)
          + ∫⁻ x, ENNReal.ofReal |quantFn n (x t)| ∂ν) := by
      have h1 : (∫⁻ x, ((1:ℝ≥0∞) + ∑ j, (ENNReal.ofReal |x j|
            + ENNReal.ofReal |quantFn n (x j)|)) ∂ν)
          = (∫⁻ _ : EuclideanSpace ℝ (Fin k), (1:ℝ≥0∞) ∂ν)
            + ∫⁻ x, (∑ j, (ENNReal.ofReal |x j|
              + ENNReal.ofReal |quantFn n (x j)|)) ∂ν :=
        lintegral_add_left measurable_const _
      have h2 : (∫⁻ x, (∑ j, (ENNReal.ofReal |x j|
            + ENNReal.ofReal |quantFn n (x j)|)) ∂ν)
          = ∑ t, ∫⁻ x, (ENNReal.ofReal |x t|
            + ENNReal.ofReal |quantFn n (x t)|) ∂ν :=
        lintegral_finsetSum _ (fun t _ => Measurable.add
          (ENNReal.measurable_ofReal.comp (measurable_coord t).abs)
          (ENNReal.measurable_ofReal.comp
            (((measurable_quantFn n).comp (measurable_coord t)).abs)))
      have h3 : ∀ t : Fin k, (∫⁻ x, (ENNReal.ofReal |x t|
            + ENNReal.ofReal |quantFn n (x t)|) ∂ν)
          = (∫⁻ x, ENNReal.ofReal |x t| ∂ν)
            + ∫⁻ x, ENNReal.ofReal |quantFn n (x t)| ∂ν :=
        fun t => lintegral_add_left
          (ENNReal.measurable_ofReal.comp (measurable_coord t).abs) _
      have h4 : (∫⁻ _ : EuclideanSpace ℝ (Fin k), (1:ℝ≥0∞) ∂ν) = 1 := by
        rw [lintegral_const, measure_univ, mul_one]
      unfold rowSumBnd
      rw [h1, h2, h4]
      congr 1
      exact Finset.sum_congr rfl (fun t _ => h3 t)
    rw [hcomp]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro t _
    apply add_le_add le_rfl
    have hqb := quant_moment_bound ν t n
    show (∫⁻ x, ENNReal.ofReal |quantFn n (x t)| ∂ν) ≤ M t + 1
    rw [hMdef]
    show (∫⁻ x, ENNReal.ofReal |quantFn n (x t)| ∂ν)
      ≤ (∫⁻ x, ENNReal.ofReal |x t| ∂ν) + 1
    exact hqb
  have hfac : ∀ n, (∫⁻ Z, ∏ r', stepFactor n j hj r' (Z r')
        ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
      = ∏ r', ∫⁻ x, stepFactor n j hj r' x ∂ν := by
    intro n
    have hindep : ProbabilityTheory.iIndepFun (fun r' Z => stepFactor n j hj r' (Z r'))
        (Measure.pi (fun _ : Fin (k+1) => ν)) :=
      ProbabilityTheory.iIndepFun_pi
        (fun r' => (measurable_stepFactor n j hj r').aemeasurable)
    have hX : ∀ r', Measurable
        (fun Z : Fin (k+1) → EuclideanSpace ℝ (Fin k) => stepFactor n j hj r' (Z r')) :=
      fun r' => (measurable_stepFactor n j hj r').comp (measurable_pi_apply r')
    have hfeq : (∫⁻ Z, ∏ r', stepFactor n j hj r' (Z r')
        ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
        = ∏ r', ∫⁻ Z, stepFactor n j hj r' (Z r')
          ∂(Measure.pi (fun _ : Fin (k+1) => ν)) :=
      ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hindep hX
    rw [hfeq]
    exact Finset.prod_congr rfl
      (fun r' _ => lintegral_row ν r' _ (measurable_stepFactor n j hj r'))
  have hPI : ∀ n, (∏ r', ∫⁻ x, stepFactor n j hj r' x ∂ν)
      ≤ (∑ t, ∫⁻ x, ENNReal.ofReal |quantVec n x t - x t| ∂ν) * C ^ k := by
    intro n
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (⟨j,hj⟩ : Fin (k+1)))]
    apply mul_le_mul _ _ zero_le zero_le
    · exact (hdiff n).le
    · have hle : ∏ r' ∈ Finset.univ.erase (⟨j,hj⟩ : Fin (k+1)),
          (∫⁻ x, stepFactor n j hj r' x ∂ν)
        ≤ ∏ r' ∈ Finset.univ.erase (⟨j,hj⟩ : Fin (k+1)), C := by
        apply Finset.prod_le_prod
        intro r' hr'
        exact hother n r' (Finset.ne_of_mem_erase hr')
      have hcard : (Finset.univ.erase (⟨j,hj⟩ : Fin (k+1))).card = k := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      rw [Finset.prod_const] at hle
      rw [hcard] at hle
      exact hle
  have hub : ∀ n, (∫⁻ Z, ENNReal.ofReal |(stepMat n Z j hj).det|
        ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
      ≤ F * ((∑ t, ∫⁻ x, ENNReal.ofReal |quantVec n x t - x t| ∂ν) * C ^ k) := by
    intro n
    calc (∫⁻ Z, ENNReal.ofReal |(stepMat n Z j hj).det| ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
        ≤ ∫⁻ Z, (F * ∏ r', stepFactor n j hj r' (Z r'))
          ∂(Measure.pi (fun _ : Fin (k+1) => ν)) := by
          apply lintegral_mono
          intro Z
          exact term_ptwise n Z j hj
      _ = F * ∏ r', ∫⁻ x, stepFactor n j hj r' x ∂ν := by
          have hc : (∫⁻ Z, (F * ∏ r', stepFactor n j hj r' (Z r'))
              ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
              = F * ∫⁻ Z, (∏ r', stepFactor n j hj r' (Z r'))
                ∂(Measure.pi (fun _ : Fin (k+1) => ν)) :=
            lintegral_const_mul F (Finset.measurable_prod _ (fun r' _ =>
              (measurable_stepFactor n j hj r').comp (measurable_pi_apply r')))
          rw [hc, hfac n]
      _ ≤ F * ((∑ t, ∫⁻ x, ENNReal.ofReal |quantVec n x t - x t| ∂ν) * C ^ k) :=
          mul_le_mul_right (hPI n) F
  have hU : Tendsto (fun n : ℕ => F * ((∑ t, ∫⁻ x,
        ENNReal.ofReal |quantVec n x t - x t| ∂ν) * C ^ k)) atTop (𝓝 0) := by
    have hL1 : ∀ t : Fin k, Tendsto
        (fun n : ℕ => ∫⁻ x, ENNReal.ofReal |quantVec n x t - x t| ∂ν) atTop (𝓝 0) :=
      fun t => quant_l1_tendsto ν t (hmom t)
    have hsum : Tendsto (fun n : ℕ => ∑ t,
          ∫⁻ x, ENNReal.ofReal |quantVec n x t - x t| ∂ν) atTop (𝓝 0) := by
      have h := tendsto_finsetSum Finset.univ (fun t _ => hL1 t)
      simpa using h
    have hmul : Tendsto (fun n : ℕ => (∑ t,
          ∫⁻ x, ENNReal.ofReal |quantVec n x t - x t| ∂ν) * C ^ k) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.mul_const hsum (Or.inr (hCk k))
      simpa using h
    have hF := ENNReal.Tendsto.const_mul hmul (Or.inr hFne)
    simpa using hF
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU
    (fun _ => zero_le) hub

/-- Determinant L1 convergence under quantization (HI-DETMONO). -/
public theorem det_l1_tendsto (ν : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin k, ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞) :
    Tendsto (fun n : ℕ => ∫⁻ Z, ENNReal.ofReal
      |simDet (fun r => quantVec n (Z r)) - simDet Z|
      ∂(Measure.pi (fun _ : Fin (k+1) => ν))) atTop (𝓝 0) := by
  have htele : ∀ n : ℕ, ∀ Z : Fin (k+1) → EuclideanSpace ℝ (Fin k),
      simDet (fun r => quantVec n (Z r)) - simDet Z
      = ∑ r : Fin (k+1), ((teleMat n Z (r.val+1)).det - (teleMat n Z r.val).det) := by
    intro n Z
    have e1 : simDet (fun r => quantVec n (Z r)) = (teleMat n Z (k+1)).det := by
      simp only [simDet, teleMat_top]
    have e2 : simDet Z = (teleMat n Z 0).det := by
      simp only [simDet, teleMat_zero]
    have hsum := Finset.sum_range_sub (fun j => (teleMat n Z j).det) (k+1)
    rw [e1, e2, ← hsum, ← Fin.sum_univ_eq_sum_range]
  have hub : ∀ n : ℕ, (∫⁻ Z, ENNReal.ofReal
        |simDet (fun r => quantVec n (Z r)) - simDet Z| ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
      ≤ ∑ r : Fin (k+1), (∫⁻ Z, ENNReal.ofReal
        |(teleMat n Z (r.val+1)).det - (teleMat n Z r.val).det|
        ∂(Measure.pi (fun _ : Fin (k+1) => ν))) := by
    intro n
    have hpt : ∀ Z : Fin (k+1) → EuclideanSpace ℝ (Fin k),
        ENNReal.ofReal |simDet (fun r => quantVec n (Z r)) - simDet Z|
          ≤ ∑ r : Fin (k+1), ENNReal.ofReal
            |(teleMat n Z (r.val+1)).det - (teleMat n Z r.val).det| := by
      intro Z
      rw [htele n Z]
      have htri := abs_sum_le_sum_abs
        (fun r : Fin (k+1) => (teleMat n Z (r.val+1)).det - (teleMat n Z r.val).det)
        Finset.univ
      have hmono := ENNReal.ofReal_le_ofReal htri
      rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => abs_nonneg _)] at hmono
      exact hmono
    calc (∫⁻ Z, ENNReal.ofReal |simDet (fun r => quantVec n (Z r)) - simDet Z|
          ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
        ≤ ∫⁻ Z, (∑ r : Fin (k+1), ENNReal.ofReal
            |(teleMat n Z (r.val+1)).det - (teleMat n Z r.val).det|)
          ∂(Measure.pi (fun _ : Fin (k+1) => ν)) := lintegral_mono (fun Z => hpt Z)
      _ = ∑ r : Fin (k+1), (∫⁻ Z, ENNReal.ofReal
          |(teleMat n Z (r.val+1)).det - (teleMat n Z r.val).det|
          ∂(Measure.pi (fun _ : Fin (k+1) => ν))) :=
          lintegral_finsetSum _ (fun r _ =>
            ENNReal.measurable_ofReal.comp
              (((measurable_teleMat_det n (r.val+1)).sub
                (measurable_teleMat_det n r.val)).abs))
  have hU : Tendsto (fun n : ℕ => ∑ r : Fin (k+1),
      (∫⁻ Z, ENNReal.ofReal |(teleMat n Z (r.val+1)).det - (teleMat n Z r.val).det|
        ∂(Measure.pi (fun _ : Fin (k+1) => ν)))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ
      (fun r _ => term_tendsto ν hmom r.val (Fin.is_lt r))
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU
    (fun _ => zero_le) hub

end DetMono

section SConv

variable {m : ℕ}

/-- Drop-last-coordinate projection (first `m` coordinates). -/
@[expose] public noncomputable def projDrop (x : EuclideanSpace ℝ (Fin (m+1))) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun t : Fin m => x t.castSucc)

/-- Applying the projection acts coordinatewise. -/
public theorem projDrop_apply (x : EuclideanSpace ℝ (Fin (m+1))) (t : Fin m) :
    projDrop x t = x t.castSucc := rfl

/-- The projection is measurable. -/
public theorem measurable_projDrop : Measurable (projDrop (m := m)) := by
  have h : Measurable (fun x : EuclideanSpace ℝ (Fin (m+1)) => fun t : Fin m => x t.castSucc) :=
    Measurable.of_eval fun t => (measurable_coord t.castSucc)
  have ho : Measurable (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) :=
    WithLp.measurable_toLp 2 (Fin m → ℝ)
  exact ho.comp h

/-- Projection commutes with coordinatewise quantization. -/
private theorem projDrop_quantVec (n : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) :
    projDrop (quantVec n x) = quantVec n (projDrop x) := by
  apply PiLp.ext
  intro t
  rfl

/-- Projected quantized law equals quantized projected law. -/
private theorem quantLaw_proj (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin (m+1)))) :
    (quantLaw n ν).map (projDrop (m := m))
      = quantLaw n (ν.map (projDrop (m := m))) := by
  rw [quantLaw, quantLaw, Measure.map_map (measurable_quantVec n) measurable_projDrop,
    Measure.map_map measurable_projDrop (measurable_quantVec n)]
  have hfun : (projDrop (m := m) ∘ quantVec n) = (quantVec n ∘ projDrop (m := m)) := by
    funext x
    exact projDrop_quantVec n x
  rw [hfun]

/-- The simplex determinant is measurable in the vertices. -/
private theorem measurable_simDet_fn (k : ℕ) : Measurable
    (fun W : Fin (k+1) → EuclideanSpace ℝ (Fin k) => simDet W) := by
  have hmat : Measurable (fun W : Fin (k+1) → EuclideanSpace ℝ (Fin k) =>
      Matrix.of (fun r c => (Fin.cases (1:ℝ) (fun t => W r t) c : ℝ))) := by
    apply Measurable.of_eval
    intro r
    apply Measurable.of_eval
    intro c
    simp only [Matrix.of_apply]
    obtain rfl | ⟨t, rfl⟩ := Fin.eq_zero_or_eq_succ c
    · simp only [Fin.cases_zero]
      exact measurable_const
    · simp only [Fin.cases_succ]
      exact (measurable_coord t).comp (measurable_pi_apply r)
  have hdet : Measurable (fun W : Fin (k+1) → EuclideanSpace ℝ (Fin k) =>
      Matrix.det (Matrix.of (fun r c => (Fin.cases (1:ℝ) (fun t => W r t) c : ℝ)))) :=
    (Continuous.matrix_det continuous_id).measurable.comp hmat
  exact hdet

/-- The simplex functional via the determinant integral. -/
private theorem S_eq_detint (k : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) :
    S k ν = ((k ! : ℕ) : ℝ≥0∞)⁻¹ * ∫⁻ Z, ENNReal.ofReal |simDet Z|
      ∂(Measure.pi (fun _ : Fin (k+1) => ν)) := by
  have hfact0 : (((k ! : ℕ)) : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.ofReal_natCast, ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos k))
  have hfactt : (((k ! : ℕ)) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hpt : ∀ Z : Fin (k+1) → EuclideanSpace ℝ (Fin k),
      volume (convexHull ℝ (Set.range Z))
        = ((k ! : ℕ) : ℝ≥0∞)⁻¹ * ENNReal.ofReal |simDet Z| := by
    intro Z
    have hbr := abs_simDet_eq_volume_convexHull (k := k) Z
    calc volume (convexHull ℝ (Set.range Z))
        = ((k ! : ℕ) : ℝ≥0∞)⁻¹ * ((((k ! : ℕ)) : ℝ≥0∞)
          * volume (convexHull ℝ (Set.range Z))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hfact0 hfactt, one_mul]
      _ = ((k ! : ℕ) : ℝ≥0∞)⁻¹ * ENNReal.ofReal |simDet Z| := by
          congr 1
          exact hbr.symm
  have hmeas : Measurable (fun Z : Fin (k+1) → EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal |simDet Z|) :=
    ENNReal.measurable_ofReal.comp (measurable_simDet_fn k).abs
  unfold S
  simp only [hpt]
  exact lintegral_const_mul _ hmeas

/-- Change of variables for the quantized simplex functional. -/
private theorem S_quant_chg (k n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν] :
    S k (quantLaw n ν) = ((k ! : ℕ) : ℝ≥0∞)⁻¹ * ∫⁻ Z, ENNReal.ofReal
      |simDet (fun r => quantVec n (Z r))| ∂(Measure.pi (fun _ : Fin (k+1) => ν)) := by
  haveI : ∀ i : Fin (k+1), SigmaFinite (ν.map (quantVec n)) := by
    haveI : IsProbabilityMeasure (ν.map (quantVec n)) := quantLaw_prob n ν
    intro i
    infer_instance
  have hpi : Measure.pi (fun _ : Fin (k+1) => quantLaw n ν)
      = (Measure.pi (fun _ : Fin (k+1) => ν)).map (fun Z r => quantVec n (Z r)) := by
    have h := Measure.pi_map_pi (μ := fun _ : Fin (k+1) => ν)
      (f := fun _ => quantVec n)
      (fun i => (measurable_quantVec (d := k) n).aemeasurable)
    simp only [quantLaw] at h ⊢
    exact h.symm
  have hmeas : Measurable (fun W : Fin (k+1) → EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal |simDet W|) :=
    ENNReal.measurable_ofReal.comp (measurable_simDet_fn k).abs
  have hT : Measurable (fun Z : Fin (k+1) → EuclideanSpace ℝ (Fin k) =>
      (fun r => quantVec n (Z r))) :=
    Measurable.of_eval fun r => (measurable_quantVec n).comp (measurable_pi_apply r)
  rw [S_eq_detint, hpi, lintegral_map hmeas hT]

/-- Pointwise reverse-triangle bound for absolute values. -/
private theorem abs_le_abs_add_abs_sub (a b : ℝ) : |a| ≤ |b| + |a - b| := by
  have h := abs_add_le b (a - b)
  have heq : b + (a - b) = a := by ring
  rw [heq] at h
  exact h

/-- S convergence under quantization (HI-SCONV). -/
public theorem S_tendsto_quant (k : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin k, ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞) :
    Tendsto (fun n : ℕ => S k (quantLaw n ν)) atTop (𝓝 (S k ν)) := by
  have hmeas : Measurable (fun W : Fin (k+1) → EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal |simDet W|) :=
    ENNReal.measurable_ofReal.comp (measurable_simDet_fn k).abs
  have hT : ∀ n : ℕ, Measurable (fun Z : Fin (k+1) → EuclideanSpace ℝ (Fin k) =>
      (fun r : Fin (k+1) => quantVec n (Z r))) := fun n =>
    Measurable.of_eval fun r => (measurable_quantVec n).comp (measurable_pi_apply r)
  have hmeasE : ∀ n : ℕ, Measurable (fun Z : Fin (k+1) → EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z|) := fun n =>
    ENNReal.measurable_ofReal.comp
      (((measurable_simDet_fn k).comp (hT n)).sub (measurable_simDet_fn k)).abs
  have hpt1 : ∀ n (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k)),
      ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r))|
      ≤ ENNReal.ofReal |simDet Z|
        + ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z| := by
    intro n Z
    calc ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r))|
        ≤ ENNReal.ofReal (|simDet Z|
            + |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z|) :=
          ENNReal.ofReal_le_ofReal (abs_le_abs_add_abs_sub _ _)
      _ = ENNReal.ofReal |simDet Z|
          + ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  have hpt2 : ∀ n (Z : Fin (k+1) → EuclideanSpace ℝ (Fin k)),
      ENNReal.ofReal |simDet Z|
      ≤ ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r))|
        + ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z| := by
    intro n Z
    have h := abs_le_abs_add_abs_sub (simDet Z) (simDet (fun r : Fin (k+1) => quantVec n (Z r)))
    rw [abs_sub_comm (simDet Z)] at h
    calc ENNReal.ofReal |simDet Z|
        ≤ ENNReal.ofReal (|simDet (fun r : Fin (k+1) => quantVec n (Z r))|
            + |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z|) :=
          ENNReal.ofReal_le_ofReal h
      _ = _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  have hmain : Tendsto (fun n : ℕ => ∫⁻ Z, ENNReal.ofReal
      |simDet (fun r : Fin (k+1) => quantVec n (Z r))| ∂(Measure.pi (fun _ : Fin (k+1) => ν))) atTop
      (𝓝 (∫⁻ Z, ENNReal.ofReal |simDet Z| ∂(Measure.pi (fun _ : Fin (k+1) => ν)))) := by
    apply tendsto_of_le_add_both _ _ (det_l1_tendsto (k := k) ν hmom)
    · intro n
      calc ∫⁻ Z, ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r))|
              ∂(Measure.pi (fun _ : Fin (k+1) => ν))
          ≤ ∫⁻ Z, (ENNReal.ofReal |simDet Z|
              + ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z|)
              ∂(Measure.pi (fun _ : Fin (k+1) => ν)) :=
            lintegral_mono (fun Z => hpt1 n Z)
        _ = (∫⁻ Z, ENNReal.ofReal |simDet Z| ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
            + ∫⁻ Z, ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z|
              ∂(Measure.pi (fun _ : Fin (k+1) => ν)) :=
            lintegral_add_left hmeas _
    · intro n
      calc ∫⁻ Z, ENNReal.ofReal |simDet Z| ∂(Measure.pi (fun _ : Fin (k+1) => ν))
          ≤ ∫⁻ Z, (ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r))|
              + ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z|)
              ∂(Measure.pi (fun _ : Fin (k+1) => ν)) :=
            lintegral_mono (fun Z => hpt2 n Z)
        _ = (∫⁻ Z, ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r))|
                ∂(Measure.pi (fun _ : Fin (k+1) => ν)))
            + ∫⁻ Z, ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r)) - simDet Z|
              ∂(Measure.pi (fun _ : Fin (k+1) => ν)) := by
            have hQ : Measurable (fun Z : Fin (k+1) → EuclideanSpace ℝ (Fin k) =>
                ENNReal.ofReal |simDet (fun r : Fin (k+1) => quantVec n (Z r))|) :=
              hmeas.comp (hT n)
            exact lintegral_add_left hQ _
  have hfact0 : ((((k ! : ℕ))) : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.ofReal_natCast, ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos k))
  have hFinv : ((((k ! : ℕ))) : ℝ≥0∞)⁻¹ ≠ ∞ :=
    fun h => hfact0 (ENNReal.inv_eq_top.mp h)
  have hSfun : ∀ n, S k (quantLaw n ν)
      = ((((k ! : ℕ))) : ℝ≥0∞)⁻¹ * ∫⁻ Z, ENNReal.ofReal
        |simDet (fun r : Fin (k+1) => quantVec n (Z r))| ∂(Measure.pi (fun _ : Fin (k+1) => ν)) :=
    fun n => S_quant_chg k n ν
  have hSlim : S k ν = ((((k ! : ℕ))) : ℝ≥0∞)⁻¹ * ∫⁻ Z, ENNReal.ofReal
      |simDet Z| ∂(Measure.pi (fun _ : Fin (k+1) => ν)) :=
    S_eq_detint k ν
  rw [hSlim]
  simp only [hSfun]
  exact ENNReal.Tendsto.const_mul hmain (Or.inr hFinv)

end SConv

section FinMoment

/-- Pushing an atomic measure through a map acts on the atoms. -/
private theorem map_atomMeas {d N d' : ℕ} (c : Fin N → ℝ≥0∞)
    (Z : Fin N → EuclideanSpace ℝ (Fin d))
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d'))
    (hf : Measurable f) :
    (atomMeas c Z).map f = atomMeas c (fun i => f (Z i)) := by
  classical
  apply Measure.ext
  intro s0 hs0
  have happly : ∀ t : Finset (Fin N),
      (∑ i ∈ t, c i • Measure.dirac (Z i)) (f ⁻¹' s0)
        = ∑ i ∈ t, (c i • Measure.dirac (Z i)) (f ⁻¹' s0) := by
    intro t
    induction t using Finset.induction with
    | empty => simp
    | insert b t hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, Measure.add_apply, ih]
  have happly2 : ∀ t : Finset (Fin N),
      (∑ i ∈ t, c i • Measure.dirac (f (Z i))) s0
        = ∑ i ∈ t, (c i • Measure.dirac (f (Z i))) s0 := by
    intro t
    induction t using Finset.induction with
    | empty => simp
    | insert b t hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, Measure.add_apply, ih]
  have hterm : ∀ (a : ℝ≥0∞) (z : EuclideanSpace ℝ (Fin d)),
      (a • Measure.dirac z) (f ⁻¹' s0) = (if f z ∈ s0 then a else 0) := by
    intro a z
    rw [Measure.smul_apply, Measure.dirac_apply]
    split_ifs with hz
    · have hz' : z ∈ f ⁻¹' s0 := hz
      rw [Set.indicator_of_mem hz']
      simp [smul_eq_mul]
    · have hz' : z ∉ f ⁻¹' s0 := hz
      rw [Set.indicator_of_notMem hz']
      simp [smul_eq_mul]
  have hterm2 : ∀ (a : ℝ≥0∞) (z : EuclideanSpace ℝ (Fin d')),
      (a • Measure.dirac z) s0 = (if z ∈ s0 then a else 0) := by
    intro a z
    rw [Measure.smul_apply, Measure.dirac_apply]
    split_ifs with hz
    · rw [Set.indicator_of_mem hz]
      simp [smul_eq_mul]
    · rw [Set.indicator_of_notMem hz]
      simp [smul_eq_mul]
  calc ((atomMeas c Z).map f) s0
      = (atomMeas c Z) (f ⁻¹' s0) := Measure.map_apply hf hs0
    _ = ∑ i, (c i • Measure.dirac (Z i)) (f ⁻¹' s0) := by
        show ((∑ i, c i • Measure.dirac (Z i)) : Measure _) (f ⁻¹' s0) = _
        exact happly Finset.univ
    _ = ∑ i, (if f (Z i) ∈ s0 then c i else 0) :=
        Finset.sum_congr rfl (fun i _ => hterm _ _)
    _ = ∑ i, (c i • Measure.dirac (f (Z i))) s0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hterm2]
    _ = (atomMeas c (fun i => f (Z i))) s0 := by
        show (∑ i, (c i • Measure.dirac (f (Z i))) s0)
          = ((∑ i, c i • Measure.dirac ((fun i => f (Z i)) i)) : Measure _) s0
        exact (happly2 Finset.univ).symm

/-- Atomic projection matches the coordinate-drop projection. -/
private theorem Yatom_eq_projDrop {m N : ℕ}
    (Z : Fin N → EuclideanSpace ℝ (Fin (m+1))) (i : Fin N) :
    Yatom Z i = projDrop (Z i) := rfl

/-- The first-moment integrand in `ofReal` form. -/
private theorem coe_nnnorm_eq_ofReal_abs {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal |x j| := by
  have h : |x j| = ((((‖x j‖₊ : ℝ≥0))) : ℝ) := by
    rw [coe_nnnorm, Real.norm_eq_abs]
  rw [h, ENNReal.ofReal_coe_nnreal]

/-- Finite first moment implies finite coordinate gap. -/
private theorem gap_lt_top_of_moment {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (j : Fin d)
    (hmom : ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞) :
    gap j ν ≠ ∞ := by
  have hF : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal |x j|) :=
    ENNReal.measurable_ofReal.comp (measurable_coord j).abs
  have hA : ∫⁻ x, ENNReal.ofReal |x j| ∂ν ≠ ∞ := by
    have hbr : ∀ x : EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal |x j| = ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) :=
      fun x => (coe_nnnorm_eq_ofReal_abs x j).symm
    simp only [hbr]
    exact hmom
  have hmarg1 : ∫⁻ p, ENNReal.ofReal |p.1 j| ∂(ν.prod ν)
      = ∫⁻ x, ENNReal.ofReal |x j| ∂ν := by
    calc ∫⁻ p, ENNReal.ofReal |p.1 j| ∂(ν.prod ν)
        = ∫⁻ p, (ENNReal.ofReal |p.1 j| * 1) ∂(ν.prod ν) := by simp [mul_one]
      _ = (∫⁻ x, ENNReal.ofReal |x j| ∂ν) * ∫⁻ y, 1 ∂ν :=
          lintegral_prod_mul hF.aemeasurable aemeasurable_const
      _ = ∫⁻ x, ENNReal.ofReal |x j| ∂ν := by rw [lintegral_one, measure_univ, mul_one]
  have hmarg2 : ∫⁻ p, ENNReal.ofReal |p.2 j| ∂(ν.prod ν)
      = ∫⁻ x, ENNReal.ofReal |x j| ∂ν := by
    calc ∫⁻ p, ENNReal.ofReal |p.2 j| ∂(ν.prod ν)
        = ∫⁻ p, (1 * ENNReal.ofReal |p.2 j|) ∂(ν.prod ν) := by simp [one_mul]
      _ = (∫⁻ x, 1 ∂ν) * ∫⁻ y, ENNReal.ofReal |y j| ∂ν :=
          lintegral_prod_mul aemeasurable_const hF.aemeasurable
      _ = ∫⁻ x, ENNReal.ofReal |x j| ∂ν := by rw [lintegral_one, measure_univ, one_mul]
  have hpt : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal |p.1 j - p.2 j|
        ≤ ENNReal.ofReal |p.1 j| + ENNReal.ofReal |p.2 j| := by
    intro p
    have habs : |p.1 j - p.2 j| ≤ |p.1 j| + |p.2 j| := by
      rw [sub_eq_add_neg]
      calc |p.1 j + -p.2 j| ≤ |p.1 j| + |-p.2 j| := abs_add_le _ _
        _ = |p.1 j| + |p.2 j| := by rw [abs_neg]
    calc ENNReal.ofReal |p.1 j - p.2 j|
        ≤ ENNReal.ofReal (|p.1 j| + |p.2 j|) := ENNReal.ofReal_le_ofReal habs
      _ = ENNReal.ofReal |p.1 j| + ENNReal.ofReal |p.2 j| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  have hAA : (∫⁻ x, ENNReal.ofReal |x j| ∂ν)
      + (∫⁻ x, ENNReal.ofReal |x j| ∂ν) ≠ ∞ :=
    lt_top_iff_ne_top.mp (ENNReal.add_lt_top.mpr
      ⟨lt_top_iff_ne_top.mpr hA, lt_top_iff_ne_top.mpr hA⟩)
  apply ne_top_of_le_ne_top hAA
  rw [gap_eq_ofReal]
  calc ∫⁻ p, ENNReal.ofReal |p.1 j - p.2 j| ∂(ν.prod ν)
      ≤ ∫⁻ p, (ENNReal.ofReal |p.1 j| + ENNReal.ofReal |p.2 j|) ∂(ν.prod ν) :=
        lintegral_mono (fun p => hpt p)
    _ = (∫⁻ p, ENNReal.ofReal |p.1 j| ∂(ν.prod ν))
        + ∫⁻ p, ENNReal.ofReal |p.2 j| ∂(ν.prod ν) := by
        have hF1 : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
            ENNReal.ofReal |p.1 j|) := hF.comp measurable_fst
        exact lintegral_add_left hF1 _
    _ = (∫⁻ x, ENNReal.ofReal |x j| ∂ν) + ∫⁻ x, ENNReal.ofReal |x j| ∂ν := by
        rw [hmarg1, hmarg2]

/-- One-step inequality for Borel probability measures with finite first moments
(HI-FINMOMENT). -/
public theorem onestep_finite_moment (m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin (m+1))))
    [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin (m+1), ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞) :
    S (m + 1) ν ≤ ENNReal.ofReal (((m + 2 : ℕ) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ)))
      * gap (Fin.last m) ν * S m (ν.map (projDrop (m := m))) := by
  have hC0 : ENNReal.ofReal (((m + 2 : ℕ) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ))) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt (by
      apply div_pos
      · exact Nat.cast_pos.mpr (by omega)
      · exact mul_pos (by norm_num) (Nat.cast_pos.mpr (by omega)))
  have hCtop : ENNReal.ofReal (((m + 2 : ℕ) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ))) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  by_cases hgap0 : gap (Fin.last m) ν = 0
  · have hS0 : S (m + 1) ν = 0 := gap_eq_zero_imp_S_eq_zero ν (Fin.last m) hgap0
    rw [hS0]
    exact zero_le
  · by_cases hSinf : S m (ν.map (projDrop (m := m))) = ∞
    · rw [hSinf, ENNReal.mul_top (mul_ne_zero hC0 hgap0)]
      exact le_top
    · have hgapTop : gap (Fin.last m) ν ≠ ∞ :=
        gap_lt_top_of_moment ν (Fin.last m) (hmom _)
      have hstep : ∀ n, S (m + 1) (quantLaw n ν)
          ≤ ENNReal.ofReal (((m + 2 : ℕ) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ)))
            * gap (Fin.last m) (quantLaw n ν)
            * S m ((quantLaw n ν).map (projDrop (m := m))) := by
        intro n
        obtain ⟨s, hsupp⟩ := quantLaw_finite_support n ν
        obtain ⟨N, p, Z, hpos, hsum, hbridge⟩ :=
          atomic_of_finite_support (quantLaw n ν) s hsupp
        have h1 := oneStep p Z hpos hsum
        have hY : atomMeas (wgt p) (Yatom Z)
            = (quantLaw n ν).map (projDrop (m := m)) := by
          have h1m : (atomMeas (wgt p) Z).map (projDrop (m := m))
              = atomMeas (wgt p) (fun i => projDrop (m := m) (Z i)) :=
            map_atomMeas _ _ _ (measurable_projDrop (m := m))
          have h2 : (fun i => projDrop (m := m) (Z i)) = Yatom Z := by
            funext i
            exact (Yatom_eq_projDrop Z i).symm
          rw [hbridge] at h1m
          rw [h2] at h1m
          exact h1m.symm
        rw [hbridge, hY] at h1
        exact h1
      have hLHS : Tendsto (fun n => S (m + 1) (quantLaw n ν)) atTop
          (𝓝 (S (m + 1) ν)) :=
        S_tendsto_quant (m + 1) ν hmom
      have hgap : Tendsto (fun n => gap (Fin.last m) (quantLaw n ν)) atTop
          (𝓝 (gap (Fin.last m) ν)) :=
        gap_quant_tendsto ν (Fin.last m) (hmom _)
      have hS : Tendsto (fun n => S m ((quantLaw n ν).map (projDrop (m := m)))) atTop
          (𝓝 (S m (ν.map (projDrop (m := m))))) := by
        have hproj : ∀ n, (quantLaw n ν).map (projDrop (m := m))
            = quantLaw n (ν.map (projDrop (m := m))) := fun n => quantLaw_proj n ν
        simp only [hproj]
        haveI : IsProbabilityMeasure (ν.map (projDrop (m := m))) := ⟨by
          simp only [Measure.map_apply (measurable_projDrop (m := m)) MeasurableSet.univ,
            Set.preimage_univ, measure_univ]⟩
        apply S_tendsto_quant m (ν.map (projDrop (m := m)))
        intro j
        have hmeas_nn : Measurable (fun x : EuclideanSpace ℝ (Fin m) =>
            ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞)) := by
          have e : (fun x : EuclideanSpace ℝ (Fin m) => ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞))
              = (fun x => ENNReal.ofReal |x j|) :=
            funext fun x => coe_nnnorm_eq_ofReal_abs x j
          rw [e]
          exact ENNReal.measurable_ofReal.comp (measurable_coord j).abs
        rw [lintegral_map hmeas_nn (measurable_projDrop (m := m))]
        simp only [projDrop_apply]
        exact hmom j.castSucc
      have hCg : Tendsto (fun n =>
          ENNReal.ofReal (((m + 2 : ℕ) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ)))
            * gap (Fin.last m) (quantLaw n ν)) atTop
          (𝓝 (ENNReal.ofReal (((m + 2 : ℕ) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ)))
            * gap (Fin.last m) ν)) :=
        ENNReal.Tendsto.const_mul hgap (Or.inr hCtop)
      have hRHS : Tendsto (fun n =>
          ENNReal.ofReal (((m + 2 : ℕ) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ)))
            * gap (Fin.last m) (quantLaw n ν)
            * S m ((quantLaw n ν).map (projDrop (m := m)))) atTop
          (𝓝 (ENNReal.ofReal (((m + 2 : ℕ) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ)))
            * gap (Fin.last m) ν * S m (ν.map (projDrop (m := m))))) :=
        ENNReal.Tendsto.mul hCg (Or.inl (mul_ne_zero hC0 hgap0)) hS
          (Or.inr (ENNReal.mul_ne_top hCtop hgapTop))
      exact le_of_tendsto_of_tendsto hLHS hRHS (Filter.Eventually.of_forall hstep)

end FinMoment

section MainBorel

/-- Projected laws of probability measures are probability measures. -/
private theorem prob_map_projDrop (m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin (m+1))))
    [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ν.map (projDrop (m := m))) := ⟨by
  simp only [Measure.map_apply (measurable_projDrop (m := m)) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]⟩

/-- Projected laws inherit finite first moments. -/
private theorem proj_moment_ne_top (m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin (m+1))))
    [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin (m+1), ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (j : Fin m) :
    ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂(ν.map (projDrop (m := m))) ≠ ∞ := by
  have hmeas_nn : Measurable (fun x : EuclideanSpace ℝ (Fin m) =>
      ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞)) := by
    have e : (fun x : EuclideanSpace ℝ (Fin m) => ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞))
        = (fun x => ENNReal.ofReal |x j|) :=
      funext fun x => coe_nnnorm_eq_ofReal_abs x j
    rw [e]
    exact ENNReal.measurable_ofReal.comp (measurable_coord j).abs
  rw [lintegral_map hmeas_nn (measurable_projDrop (m := m))]
  simp only [projDrop_apply]
  exact hmom j.castSucc

/-- Projected coordinate gaps agree with the original ones (HI-PROJGAP). -/
public theorem gap_map_projDrop (m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin (m+1))))
    [SFinite ν] (j : Fin m) :
    gap j (ν.map (projDrop (m := m))) = gap j.castSucc ν := by
  have hmeas : Measurable (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
      ENNReal.ofReal |q.1 j - q.2 j|) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_coord j).comp measurable_fst).sub
        ((measurable_coord j).comp measurable_snd)).abs
  have hmap : Measurable (Prod.map (projDrop (m := m)) (projDrop (m := m)) :
      EuclideanSpace ℝ (Fin (m+1)) × EuclideanSpace ℝ (Fin (m+1)) → _) :=
    (measurable_projDrop (m := m)).prodMap (measurable_projDrop (m := m))
  rw [gap_eq_ofReal, gap_eq_ofReal,
    map_prod_map _ _ (measurable_projDrop (m := m)) (measurable_projDrop (m := m)),
    lintegral_map hmeas hmap]
  apply lintegral_congr_ae
  filter_upwards with p
  simp only [Prod.map_fst, Prod.map_snd, projDrop_apply]

/-- HI-MAIN: random-simplex inequality for Borel laws with finite first moments,
with the exact manuscript constant `(d+1)/2^d`. -/
public theorem main_borel (m : ℕ) :
    ∀ (ν : Measure (EuclideanSpace ℝ (Fin (m + 1)))),
    [IsProbabilityMeasure ν] →
    (∀ j : Fin (m + 1), ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞) →
    S (m + 1) ν
    ≤ ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
      * ∏ j : Fin (m + 1), gap j ν := by
  induction m with
  | zero =>
    intro ν hinst hmom
    haveI := hinst
    have hconst1 : ENNReal.ofReal (((((0 + 2 : ℕ)) : ℝ) / 2 ^ (0 + 1))) = 1 := by
      have e : ((((0 + 2 : ℕ)) : ℝ) / 2 ^ (0 + 1)) = 1 := by
        push_cast
        norm_num
      rw [e, ENNReal.ofReal_one]
    have hprod : (∏ j : Fin (0 + 1), gap j ν) = gap (Fin.last 0) ν :=
      Fin.prod_univ_one _
    rw [hconst1, hprod, one_mul]
    exact le_of_eq (oneDimS_eq_gap ν (Fin.last 0))
  | succ m ih =>
    intro ν hinst hmom
    haveI := hinst
    have h1 := onestep_finite_moment (m + 1) ν hmom
    haveI hproj : IsProbabilityMeasure (ν.map (projDrop (m := m + 1))) :=
      prob_map_projDrop (m + 1) ν
    have hmomP : ∀ j : Fin (m + 1),
        ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂(ν.map (projDrop (m := m + 1))) ≠ ∞ :=
      fun j => proj_moment_ne_top (m + 1) ν hmom j
    have h2 := ih (ν.map (projDrop (m := m + 1))) hmomP
    have hgap : ∀ j : Fin (m + 1),
        gap j (ν.map (projDrop (m := m + 1))) = gap j.castSucc ν := by
      intro j
      exact gap_map_projDrop (m + 1) ν j
    have hP : (∏ j : Fin (m + 1), gap j (ν.map (projDrop (m := m + 1))))
        = ∏ j : Fin (m + 1), gap j.castSucc ν :=
      Finset.prod_congr rfl (fun j _ => hgap j)
    rw [hP] at h2
    have h3 := h1.trans (mul_le_mul_right h2 _)
    have hsplit : (∏ j : Fin (m + 1 + 1), gap j ν)
        = (∏ j : Fin (m + 1), gap j.castSucc ν)
          * gap (Fin.last (m + 1)) ν :=
      Fin.prod_univ_castSucc _
    rw [hsplit]
    calc S (m + 1 + 1) ν
        ≤ ENNReal.ofReal (((((m + 1) + 2 : ℕ)) : ℝ)
            / (2 * ((((m + 1) + 1 : ℕ)) : ℝ)))
          * gap (Fin.last (m + 1)) ν
          * (ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
            * ∏ j : Fin (m + 1), gap j.castSucc ν) := h3
      _ = ENNReal.ofReal (((((m + 1) + 2 : ℕ)) : ℝ) / 2 ^ ((m + 1) + 1))
          * ((∏ j : Fin (m + 1), gap j.castSucc ν)
            * gap (Fin.last (m + 1)) ν) := by
          rw [← scalar_induction m]
          ring

/-- HI-MAIN (full): the manuscript random-simplex inequality with no moment
hypothesis — zero gaps force `S = 0`, infinite gaps make the RHS `∞`. -/
public theorem main_full (m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin (m + 1))))
    [IsProbabilityMeasure ν] :
    S (m + 1) ν
    ≤ ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
      * ∏ j : Fin (m + 1), gap j ν := by
  by_cases h0 : ∃ j, gap j ν = 0
  · obtain ⟨j, hj⟩ := h0
    have hS0 : S (m + 1) ν = 0 := gap_eq_zero_imp_S_eq_zero ν j hj
    rw [hS0]
    exact zero_le
  · push Not at h0
    by_cases hinf : ∃ j, gap j ν = ∞
    · obtain ⟨j, hj⟩ := hinf
      have hC0 : ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1))) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero]
        exact not_le_of_gt (by
          apply div_pos
          · exact Nat.cast_pos.mpr (by omega)
          · exact pow_pos (by norm_num) _)
      have hrest : ∏ i ∈ Finset.univ.erase j, gap i ν ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i _
        exact h0 i
      have h1 : gap j ν * ∏ i ∈ Finset.univ.erase j, gap i ν
          = ∏ i, gap i ν :=
        Finset.mul_prod_erase _ (fun i => gap i ν) (Finset.mem_univ j)
      have htop : (∞ : ℝ≥0∞) * ∏ i ∈ Finset.univ.erase j, gap i ν = ∞ := by
        rw [mul_comm]
        exact ENNReal.mul_top hrest
      rw [hj] at h1
      rw [htop] at h1
      have hprod : ∏ j : Fin (m + 1), gap j ν = ∞ := h1.symm
      rw [hprod, ENNReal.mul_top hC0]
      exact le_top
    · push Not at hinf
      have hmom : ∀ j : Fin (m + 1),
          ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞ := by
        intro j
        exact lt_top_iff_ne_top.mp
          (finite_gap_moment ν j (lt_top_iff_ne_top.mpr (hinf j)))
      exact main_borel m ν hmom

end MainBorel

end HypercubeInequality
