module

/-
# Normalized coordinate-projection ratios (paper §12, Proposition 12.1)

For a probability law `ν` on `ℝ^k` with positive coordinate gaps, the paper
defines the normalized ratio

`R(ν) = 2^k * S_k(ν) / ((k+1) * ∏ j, D_j(ν))`,

so that Theorem 1.1 is `R(ν) ≤ 1`.  Proposition 12.1 asserts monotonicity
under coordinate deletion: deleting one coordinate cannot increase `R`.

This module formalizes, in `ℝ≥0∞` (division is only used under explicit
positive-finite denominator hypotheses, so the algebra is justified):

* `subsetRatio_le_one` — `R(ν) ≤ 1` from `main_borel`;
* `subsetRatio_one_eq_one` — singleton equality `R = 1` in dimension one
  (paper: `S_1 = D_1` by definition);
* `subsetRatio_succ_le_proj` — the one-coordinate deletion step
  `R_{m+1}(ν) ≤ R_m(ν.map projDrop)`, from `onestep_finite_moment`
  (Corollary 7.1) and `gap_map_projDrop`;
* `subsetRatio_le_of_proj_le` — persistence of deficit: any upper bound on
  the projected ratio bounds the full ratio.

The remaining step for the literal Proposition 12.1 over arbitrary
`J ⊆ I` is iteration of the deletion step over a coordinate permutation
identifying `ν_I` with iterated `projDrop` pushforwards; that permutation
bridge is recorded as a gap in `coverage.csv` (HI-RATIO-SUBSET), not
claimed here.
-/

public import Section_7_Approximation.Approx

namespace HypercubeInequality

open MeasureTheory Measure Filter Topology
open scoped ENNReal NNReal

/-- Normalized ratio `R(ν) = 2^k S_k(ν) / ((k+1) ∏ D_j(ν))` (§12). -/
@[expose] public noncomputable def subsetRatio (k : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin k))) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ k / (k + 1 : ℝ)) * S k ν / ∏ j : Fin k, gap j ν

/-- Finite first moments bound the gaps: `D_j(ν) ≤ 2 E|X^{(j)}| < ∞`. -/
public theorem gap_ne_top_of_moment {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (j : Fin d)
    (hmom : ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞) :
    gap j ν ≠ ∞ := by
  have hbound : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ((‖p.1 j - p.2 j‖₊ : ℝ≥0) : ℝ≥0∞)
        ≤ ((‖p.1 j‖₊ : ℝ≥0) : ℝ≥0∞) + ((‖p.2 j‖₊ : ℝ≥0) : ℝ≥0∞) := by
    intro p
    have h : ‖p.1 j - p.2 j‖₊ ≤ ‖p.1 j‖₊ + ‖p.2 j‖₊ := by
      calc ‖p.1 j - p.2 j‖₊ = ‖p.1 j + (-p.2 j)‖₊ := by rw [sub_eq_add_neg]
        _ ≤ ‖p.1 j‖₊ + ‖-p.2 j‖₊ := nnnorm_add_le _ _
        _ = ‖p.1 j‖₊ + ‖p.2 j‖₊ := by rw [nnnorm_neg]
    exact_mod_cast h
  have hle : gap j ν
      ≤ ∫⁻ p, (((‖p.1 j‖₊ : ℝ≥0) : ℝ≥0∞) + ((‖p.2 j‖₊ : ℝ≥0) : ℝ≥0∞))
          ∂(ν.prod ν) :=
    lintegral_mono hbound
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
      ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞)) :=
    (measurable_coe_nnreal_ennreal.comp (measurable_coord j).nnnorm)
  have hf1 : (∫⁻ p, ((‖p.1 j‖₊ : ℝ≥0) : ℝ≥0∞) ∂(ν.prod ν))
      = ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν := by
    simpa using lintegral_prod_mul (μ := ν) (ν := ν) hmeas.aemeasurable
      (measurable_const : Measurable (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ≥0∞))).aemeasurable
  have hf2 : (∫⁻ p, ((‖p.2 j‖₊ : ℝ≥0) : ℝ≥0∞) ∂(ν.prod ν))
      = ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν := by
    simpa using lintegral_prod_mul (μ := ν) (ν := ν)
      (measurable_const : Measurable (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ≥0∞))).aemeasurable
      hmeas.aemeasurable
  have hadd : ∫⁻ p, (((‖p.1 j‖₊ : ℝ≥0) : ℝ≥0∞) + ((‖p.2 j‖₊ : ℝ≥0) : ℝ≥0∞))
        ∂(ν.prod ν)
      = (∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν)
        + ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν := by
    have hfm : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ((‖p.1 j‖₊ : ℝ≥0) : ℝ≥0∞)) := hmeas.comp measurable_fst
    rw [lintegral_add_left hfm _, hf1, hf2]
  rw [hadd] at hle
  intro h
  rw [h] at hle
  exact hmom ((ENNReal.add_eq_top.mp (top_le_iff.mp hle)).elim id id)

/-- `R(ν) ≤ 1` under finite moments and positive finite gaps (Thm 1.1). -/
public theorem subsetRatio_le_one (m : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin (m + 1))))
    [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin (m + 1), ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (hpos : ∀ j : Fin (m + 1), gap j ν ≠ 0) :
    subsetRatio (m + 1) ν ≤ 1 := by
  have hfin : ∀ j : Fin (m + 1), gap j ν ≠ ∞ :=
    fun j => gap_ne_top_of_moment ν j (hmom j)
  have hP : (∏ j : Fin (m + 1), gap j ν) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hpos j)
  have hPtop : (∏ j : Fin (m + 1), gap j ν) ≠ ∞ :=
    ENNReal.prod_ne_top (fun j _ => hfin j)
  have hmain := main_borel m ν hmom
  have hC : ENNReal.ofReal ((2 : ℝ) ^ (m + 1) / ((((m + 1 : ℕ)) : ℝ) + 1))
      * (ENNReal.ofReal ((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1))
        * ∏ j : Fin (m + 1), gap j ν)
      = ∏ j : Fin (m + 1), gap j ν := by
    have h1 : (2 : ℝ) ^ (m + 1) / ((((m + 1 : ℕ)) : ℝ) + 1)
        * ((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)) = 1 := by
      have hm1 : (((m + 1 : ℕ)) : ℝ) + 1 = (((m + 2 : ℕ)) : ℝ) := by push_cast; ring
      rw [hm1]
      field_simp
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), h1, ENNReal.ofReal_one, one_mul]
  rw [subsetRatio, ENNReal.div_le_iff hP hPtop]
  calc ENNReal.ofReal ((2 : ℝ) ^ (m + 1) / ((((m + 1 : ℕ)) : ℝ) + 1)) * S (m + 1) ν
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (m + 1) / ((((m + 1 : ℕ)) : ℝ) + 1))
        * (ENNReal.ofReal ((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1))
          * ∏ j : Fin (m + 1), gap j ν) :=
        mul_le_mul' le_rfl hmain
    _ = ∏ j : Fin (m + 1), gap j ν := hC
    _ = 1 * ∏ j : Fin (m + 1), gap j ν := (one_mul _).symm

/-- Singleton equality: in dimension one `R = 1` (paper §12). -/
public theorem subsetRatio_one_eq_one
    (ν : Measure (EuclideanSpace ℝ (Fin 1)))
    [IsProbabilityMeasure ν]
    (hpos : gap (0 : Fin 1) ν ≠ 0)
    (hfin : gap (0 : Fin 1) ν ≠ ∞) :
    subsetRatio 1 ν = 1 := by
  have hprod : (∏ j : Fin 1, gap j ν) = gap (0 : Fin 1) ν :=
    Fin.prod_univ_one _
  have hS : S 1 ν = gap (0 : Fin 1) ν := oneDimS_eq_gap ν 0
  have hcoef : ENNReal.ofReal ((2 : ℝ) ^ 1 / (((1 : ℕ) : ℝ) + 1)) = 1 := by
    norm_num
  rw [subsetRatio, hprod, hcoef, one_mul, hS]
  exact ENNReal.div_self hpos hfin

/-- One-coordinate deletion step of Proposition 12.1:
`R_{m+1}(ν) ≤ R_m(proj ν)` for the drop-last projection. -/
public theorem subsetRatio_succ_le_proj (m : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin (m + 1))))
    [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin (m + 1), ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (hpos : ∀ j : Fin (m + 1), gap j ν ≠ 0) :
    subsetRatio (m + 1) ν ≤ subsetRatio m (ν.map (projDrop (m := m))) := by
  have hfin : ∀ j : Fin (m + 1), gap j ν ≠ ∞ :=
    fun j => gap_ne_top_of_moment ν j (hmom j)
  have : IsProbabilityMeasure (ν.map (projDrop (m := m))) := ⟨by
    simp only [Measure.map_apply (measurable_projDrop (m := m))
      MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  have hfinP : ∀ j : Fin m, gap j (ν.map (projDrop (m := m))) ≠ ∞ := by
    intro j
    rw [gap_map_projDrop m ν j]
    exact hfin j.castSucc
  have hposP : ∀ j : Fin m, gap j (ν.map (projDrop (m := m))) ≠ 0 := by
    intro j
    rw [gap_map_projDrop m ν j]
    exact hpos j.castSucc
  have hstep := onestep_finite_moment m ν hmom
  have hsplit : (∏ j : Fin (m + 1), gap j ν)
      = (∏ j : Fin m, gap j.castSucc ν) * gap (Fin.last m) ν :=
    Fin.prod_univ_castSucc _
  have hgapP : (∏ j : Fin m, gap j (ν.map (projDrop (m := m))))
      = ∏ j : Fin m, gap j.castSucc ν :=
    Finset.prod_congr rfl (fun j _ => gap_map_projDrop m ν j)
  have hPlast : gap (Fin.last m) ν ≠ 0 := hpos _
  have hPlastTop : gap (Fin.last m) ν ≠ ∞ := hfin _
  have hP : (∏ j : Fin (m + 1), gap j ν) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hpos j)
  have hPtop : (∏ j : Fin (m + 1), gap j ν) ≠ ∞ :=
    ENNReal.prod_ne_top (fun j _ => hfin j)
  have hPP : (∏ j : Fin m, gap j (ν.map (projDrop (m := m)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hposP j)
  have hPPtop : (∏ j : Fin m, gap j (ν.map (projDrop (m := m)))) ≠ ∞ :=
    ENNReal.prod_ne_top (fun j _ => hfinP j)
  have hcoef : ENNReal.ofReal ((2 : ℝ) ^ (m + 1) / ((((m + 1 : ℕ)) : ℝ) + 1))
        * ENNReal.ofReal ((((m + 2 : ℕ)) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ)))
      = ENNReal.ofReal ((2 : ℝ) ^ m / ((((m : ℕ)) : ℝ) + 1)) := by
    have h1 : (2 : ℝ) ^ (m + 1) / ((((m + 1 : ℕ)) : ℝ) + 1)
        * ((((m + 2 : ℕ)) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ)))
        = (2 : ℝ) ^ m / ((((m : ℕ)) : ℝ) + 1) := by
      have hm2 : (((m + 2 : ℕ)) : ℝ) = (((m + 1 : ℕ)) : ℝ) + 1 := by push_cast; ring
      have hm1 : (((m + 1 : ℕ)) : ℝ) = ((m : ℕ) : ℝ) + 1 := by push_cast; ring
      have hA : ((m : ℝ) + 1 + 1) ≠ 0 :=
        ne_of_gt (by positivity : (0 : ℝ) < (m : ℝ) + 1 + 1)
      rw [hm2, hm1]
      calc (2 : ℝ) ^ (m + 1) / ((m : ℝ) + 1 + 1)
            * (((m : ℝ) + 1 + 1) / (2 * ((m : ℝ) + 1)))
          = (2 : ℝ) ^ (m + 1) / (2 * ((m : ℝ) + 1)) := by
            rw [div_mul_div_comm, mul_comm ((2 : ℝ) ^ (m + 1)) ((m : ℝ) + 1 + 1),
              mul_div_mul_left _ _ hA]
        _ = (2 : ℝ) ^ m / ((m : ℝ) + 1) := by
            rw [pow_succ, mul_comm ((2 : ℝ) ^ m) 2,
              mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← ENNReal.ofReal_mul (by positivity), h1]
  have hPP0 : (∏ j : Fin m, gap j.castSucc ν) ≠ 0 := hgapP ▸ hPP
  have hPP0top : (∏ j : Fin m, gap j.castSucc ν) ≠ ∞ := hgapP ▸ hPPtop
  rw [subsetRatio, subsetRatio, hgapP, ENNReal.div_le_iff hP hPtop, hsplit]
  calc ENNReal.ofReal ((2 : ℝ) ^ (m + 1) / ((((m + 1 : ℕ)) : ℝ) + 1)) * S (m + 1) ν
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (m + 1) / ((((m + 1 : ℕ)) : ℝ) + 1))
        * (ENNReal.ofReal ((((m + 2 : ℕ)) : ℝ) / (2 * ((m + 1 : ℕ) : ℝ)))
          * gap (Fin.last m) ν * S m (ν.map (projDrop (m := m)))) :=
        mul_le_mul' le_rfl hstep
    _ = ENNReal.ofReal ((2 : ℝ) ^ m / ((((m : ℕ)) : ℝ) + 1))
        * S m (ν.map (projDrop (m := m))) * gap (Fin.last m) ν := by
        rw [← hcoef]; ring
    _ = (ENNReal.ofReal ((2 : ℝ) ^ m / ((((m : ℕ)) : ℝ) + 1))
        * S m (ν.map (projDrop (m := m))) / ∏ j : Fin m, gap j.castSucc ν)
        * ((∏ j : Fin m, gap j.castSucc ν) * gap (Fin.last m) ν) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel hPP0 hPP0top]

/-- Persistence of deficit: an upper bound on the projected ratio bounds
the full ratio (§12 consequence). -/
public theorem subsetRatio_le_of_proj_le (m : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin (m + 1))))
    [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin (m + 1), ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (hpos : ∀ j : Fin (m + 1), gap j ν ≠ 0) (c : ℝ≥0∞)
    (hc : subsetRatio m (ν.map (projDrop (m := m))) ≤ c) :
    subsetRatio (m + 1) ν ≤ c :=
  (subsetRatio_succ_le_proj m ν hmom hpos).trans hc

end HypercubeInequality
