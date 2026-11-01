module

/-
# Simplex determinant-volume bridge (HI-SIMPVOL)

For `v : Fin (k+1) → EuclideanSpace ℝ (Fin k)`:
`volume (convexHull ℝ (Set.range v)) = |simDet v| / k!`.

Route: the convex hull is the image of the coordinate simplex
`Δ = {u | ∀ j, 0 ≤ u j ∧ ∑ u ≤ 1}` under the affine map
`u ↦ v 0 + Ψ' u`, where `Ψ'` is the endomorphism with
`Ψ' e_j = v_{j+1} - v 0`. The volume of `Δ` is `1/k!` (Fubini induction),
the linear image scales by `|det Ψ'|`, and `det Ψ' = simDet v` (row
operations + cofactor expansion). The degenerate case is free since
`addHaar_image_linearMap` needs no nonsingularity hypothesis.
-/

public import Mathlib
public import Section_1_Introduction.Core

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

/-- The coordinate `k`-simplex: nonnegative vectors with sum at most one. -/
@[expose] public def stdSimplexPi (k : ℕ) : Set (Fin k → ℝ) :=
  {u | (∀ j, 0 ≤ u j) ∧ ∑ j, u j ≤ 1}

public theorem measurableSet_stdSimplexPi (k : ℕ) :
    MeasurableSet (stdSimplexPi k) := by
  rw [stdSimplexPi, Set.ofPred_and]
  apply MeasurableSet.inter
  · have hset : {u : Fin k → ℝ | ∀ j, 0 ≤ u j} = ⋂ j, {u | 0 ≤ u j} := by
      ext u
      simp [Set.mem_iInter]
    rw [hset]
    apply MeasurableSet.iInter
    intro j
    have hpre : {u : Fin k → ℝ | 0 ≤ u j} = (fun u => u j) ⁻¹' Set.Ici 0 := rfl
    rw [hpre]
    exact isClosed_Ici.preimage (continuous_apply j) |>.measurableSet
  · have hcont : Continuous fun u : Fin k → ℝ => ∑ j, u j :=
      continuous_finsetSum _ fun j _ => continuous_apply j
    have hpre : {u : Fin k → ℝ | ∑ j, u j ≤ 1} = (fun u => ∑ j, u j) ⁻¹' Set.Iic 1 :=
      rfl
    rw [hpre]
    exact isClosed_Iic.preimage hcont |>.measurableSet

public theorem volume_stdSimplexPi_zero : volume (stdSimplexPi 0) = 1 := by
  have hset : stdSimplexPi 0 = Set.univ := by
    ext u
    simp [stdSimplexPi]
  rw [hset, volume_pi_eq_dirac]
  simp

/-- Determinant of `mulVecLin`: reduces to the matrix determinant. -/
public theorem det_mulVecLin {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
    LinearMap.det (Matrix.mulVecLin M) = Matrix.det M := by
  rw [← Matrix.toLin'_apply', LinearMap.det_toLin']

/-- The fiber of the head-coordinate split over `t` is the `(1-t)`-scaling
of the `k`-simplex. Membership form. -/
public theorem mem_fiber_stdSimplexPi {k : ℕ} (t : ℝ) (w : Fin k → ℝ)
    (e : (Fin (k + 1) → ℝ) ≃ᵐ ℝ × (Fin k → ℝ))
    (hsymm : ∀ p : ℝ × (Fin k → ℝ), e.symm p = Fin.cons p.1 p.2) :
    e.symm (t, w) ∈ stdSimplexPi (k + 1) ↔
      0 ≤ t ∧ (∀ j, 0 ≤ w j) ∧ t + ∑ j, w j ≤ 1 := by
  rw [hsymm]
  simp only [stdSimplexPi, Set.mem_ofPred_eq]
  constructor
  · intro h
    obtain ⟨hpos, hsum⟩ := h
    rw [Fin.forall_fin_succ] at hpos
    simp only [Fin.cons_zero, Fin.cons_succ] at hpos
    rw [Fin.sum_univ_succ] at hsum
    simp only [Fin.cons_zero, Fin.cons_succ] at hsum
    exact ⟨hpos.1, hpos.2, by linarith⟩
  · intro h
    obtain ⟨ht, hwpos, hsum⟩ := h
    constructor
    · rw [Fin.forall_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact ⟨ht, hwpos⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      linarith

/-- Volume of the coordinate simplex by Fubini induction. -/
public theorem volume_stdSimplexPi_succ (k : ℕ)
    (IH : volume (stdSimplexPi k) = ((k ! : ℕ) : ℝ≥0∞)⁻¹) :
    volume (stdSimplexPi (k + 1)) = ((((k + 1) ! : ℕ)) : ℝ≥0∞)⁻¹ := by
  have hhaar : IsAddHaarMeasure (volume : Measure (Fin k → ℝ)) :=
    isAddHaarMeasure_volume_pi _
  set e : (Fin (k + 1) → ℝ) ≃ᵐ ℝ × (Fin k → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0 with hedef
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove _ 0
  have hsymm_map : Measure.map e.symm volume = volume := by
    calc Measure.map e.symm volume
        = Measure.map e.symm (Measure.map e volume) := by rw [hmp.2]
      _ = Measure.map (e.symm ∘ e) volume :=
          Measure.map_map e.symm.measurable e.measurable
      _ = volume := by simp
  have hsymm_cons : ∀ p : ℝ × (Fin k → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p
    rw [hedef]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
      Fin.consEquiv_apply]
  have hmeas_ind : Measurable
      ((stdSimplexPi (k + 1)).indicator (1 : (Fin (k + 1) → ℝ) → ℝ≥0∞)) :=
    Measurable.indicator measurable_one (measurableSet_stdSimplexPi _)
  have hvol : volume (stdSimplexPi (k + 1))
      = ∫⁻ p : ℝ × (Fin k → ℝ),
        (stdSimplexPi (k + 1)).indicator 1 (e.symm p) ∂(volume.prod volume) := by
    rw [← lintegral_indicator_one (measurableSet_stdSimplexPi (k + 1)),
      ← hsymm_map, lintegral_map hmeas_ind e.symm.measurable,
      Measure.volume_eq_prod]
  have haemeas : AEMeasurable
      (fun p : ℝ × (Fin k → ℝ) => (stdSimplexPi (k + 1)).indicator 1 (e.symm p))
      (volume.prod volume) :=
    (hmeas_ind.comp e.symm.measurable).aemeasurable
  -- Fiber volume: scaling identity
  have hfiber : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      volume {w : Fin k → ℝ | e.symm (t, w) ∈ stdSimplexPi (k + 1)}
        = ENNReal.ofReal ((1 - t) ^ k) * ((k ! : ℕ) : ℝ≥0∞)⁻¹ := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have hscale : {w : Fin k → ℝ | e.symm (t, w) ∈ stdSimplexPi (k + 1)}
        = ((1 - t) • LinearMap.id : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) ''
          stdSimplexPi k := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      rw [mem_fiber_stdSimplexPi t w e hsymm_cons]
      constructor
      · intro h
        obtain ⟨ht0, hwpos, hsum⟩ := h
        by_cases ht1 : t = 1
        · subst ht1
          have hle : ∑ j, w j ≤ 0 := by linarith
          have hnn : ∀ j ∈ Finset.univ, 0 ≤ w j := fun j _ => hwpos j
          have hsum0 : ∑ j, w j = 0 :=
            le_antisymm hle (Finset.sum_nonneg hnn)
          have hw0 : w = 0 := by
            have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
            funext j
            exact hall j (Finset.mem_univ j)
          refine ⟨0, ⟨fun j => le_refl 0, by simp⟩, ?_⟩
          simp [hw0]
        · have hpos : 0 < 1 - t :=
            sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
          refine ⟨(1 - t)⁻¹ • w, ⟨?_, ?_⟩, ?_⟩
          · intro j
            simp only [Pi.smul_apply, smul_eq_mul]
            exact mul_nonneg (le_of_lt (inv_pos.mpr hpos)) (hwpos j)
          · have hsumw : ∑ j, ((1 - t)⁻¹ • w) j = (1 - t)⁻¹ * ∑ j, w j := by
              simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
            rw [hsumw]
            have hle : ∑ j, w j ≤ 1 - t := by linarith
            calc (1 - t)⁻¹ * ∑ j, w j ≤ (1 - t)⁻¹ * (1 - t) :=
                  mul_le_mul_of_nonneg_left hle (le_of_lt (inv_pos.mpr hpos))
              _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
          · show ((1 - t) • LinearMap.id) ((1 - t)⁻¹ • w) = w
            rw [LinearMap.smul_apply, LinearMap.id_apply, ← smul_assoc, smul_eq_mul,
              mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
      · intro h
        obtain ⟨u, hu, rfl⟩ := h
        obtain ⟨hupos, husum⟩ := hu
        have hw : ∀ j, (((1 - t) • LinearMap.id :
            (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) u) j = (1 - t) * u j := by
          intro j
          simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply,
            smul_eq_mul]
        refine ⟨ht.1, fun j => ?_, ?_⟩
        · rw [hw j]
          exact mul_nonneg (by linarith) (hupos j)
        · have hsumw : ∑ j, (((1 - t) • LinearMap.id :
              (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) u) j
              = (1 - t) * ∑ j, u j := by
            simp only [hw, ← Finset.mul_sum]
          rw [hsumw]
          have hle : (1 - t) * ∑ j, u j ≤ (1 - t) * 1 :=
            mul_le_mul_of_nonneg_left husum (by linarith)
          linarith
    rw [hscale, addHaar_image_linearMap]
    have hsmul : ((1 - t) • LinearMap.id : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))
        = Matrix.mulVecLin ((1 - t) • 1) := by
      apply LinearMap.ext
      intro w
      ext j
      simp only [LinearMap.smul_apply, LinearMap.id_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        have h1 : (1 : Matrix (Fin k) (Fin k) ℝ) j i = 0 :=
          Matrix.one_apply_ne (Ne.symm hij)
        simp only [Matrix.smul_apply, h1, smul_zero, zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hdet : LinearMap.det ((1 - t) • LinearMap.id : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))
        = (1 - t) ^ k := by
      rw [hsmul, det_mulVecLin, Matrix.det_smul, Matrix.det_one, mul_one,
        Fintype.card_fin]
    rw [hdet]
    have hnn : 0 ≤ (1 - t) ^ k := pow_nonneg (by linarith) k
    rw [abs_of_nonneg hnn, IH]
  -- Inner integral as fiber volume
  have hinner_vol : ∀ t : ℝ,
      (∫⁻ w, (stdSimplexPi (k + 1)).indicator 1 (e.symm (t, w)) ∂volume)
        = volume {w : Fin k → ℝ | e.symm (t, w) ∈ stdSimplexPi (k + 1)} := by
    intro t
    have hmfiber : MeasurableSet
        {w : Fin k → ℝ | e.symm (t, w) ∈ stdSimplexPi (k + 1)} :=
      (e.symm.measurable.comp
        (measurable_const.prodMk measurable_id)) (measurableSet_stdSimplexPi _)
    rw [← lintegral_indicator_one hmfiber]
    apply lintegral_congr_ae
    filter_upwards with w
    rfl
  -- Pointwise inner formula (ae: correct except possibly at t = 0)
  have hae0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    have hnull : volume ({0} : Set ℝ) = 0 := by simp
    have hset : {t : ℝ | ¬ t ≠ 0} = {0} := by
      ext t
      simp
    rw [hset]
    exact hnull
  have hinner_ae : (fun t : ℝ => ∫⁻ w,
          (stdSimplexPi (k + 1)).indicator 1 (e.symm (t, w)) ∂volume)
      =ᵐ[volume] (Set.Ioc (0 : ℝ) 1).indicator
        (fun t => ENNReal.ofReal ((1 - t) ^ k) * ((k ! : ℕ) : ℝ≥0∞)⁻¹) := by
    filter_upwards [hae0] with t htne
    rw [hinner_vol]
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht,
        hfiber t (Set.Ioc_subset_Icc_self ht)]
    · rw [Set.indicator_of_notMem ht]
      have hempty : {w : Fin k → ℝ | e.symm (t, w) ∈ stdSimplexPi (k + 1)}
          = ∅ := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hmem
        rw [mem_fiber_stdSimplexPi t w e hsymm_cons] at hmem
        obtain ⟨ht0, hwpos, hsum⟩ := hmem
        have hle1 : t ≤ 1 := by
          have hnn : 0 ≤ ∑ j, w j := Finset.sum_nonneg (fun j _ => hwpos j)
          linarith
        exact ht ⟨lt_of_le_of_ne ht0 (fun h => htne h.symm), hle1⟩
      rw [hempty]
      simp
  rw [hvol, lintegral_prod _ haemeas, lintegral_congr_ae hinner_ae,
    lintegral_indicator measurableSet_Ioc]
  have hmeasF : Measurable fun t : ℝ => ENNReal.ofReal ((1 - t) ^ k) :=
    Measurable.ennreal_ofReal
      (((continuous_const.sub continuous_id).pow k).measurable)
  rw [lintegral_mul_const _ hmeasF]
  have hpow : (∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ k) ∂volume)
      = ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    have hintIcc : IntegrableOn (fun t : ℝ => (1 - t) ^ k) (Set.Icc 0 1) volume :=
      ((continuous_const.sub continuous_id).pow k).continuousOn.integrableOn_compact
        isCompact_Icc
    have hint : Integrable (fun t : ℝ => (1 - t) ^ k)
        (volume.restrict (Set.Ioc 0 1)) :=
      (hintIcc.mono_set Set.Ioc_subset_Icc_self).integrable
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)]
        fun t : ℝ => (1 - t) ^ k := by
      have hmem : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          t ∈ Set.Ioc (0:ℝ) 1 :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hmem] with t ht
      rw [Set.mem_Ioc] at ht
      exact pow_nonneg (by linarith) k
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le zero_le_one]
    show (∫ t in (0:ℝ)..1, (1 - t) ^ k ∂volume) = 1 / ((k : ℝ) + 1)
    have hsub : (∫ t in (0:ℝ)..1, (1 - t) ^ k ∂volume)
        = ∫ u in (1:ℝ)-1..1-0, u ^ k ∂volume :=
      intervalIntegral.integral_comp_sub_left (f := fun u : ℝ => u ^ k) (d := 1)
    rw [hsub]
    simp only [sub_self, sub_zero]
    rw [integral_pow, one_pow, zero_pow (by omega : k + 1 ≠ 0), sub_zero]
  rw [hpow]
  -- Constant algebra: ofReal (1/(k+1)) * (k!)⁻¹ = ((k+1)!)⁻¹
  have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hfac : (0:ℝ) < ((k)! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hfacrw : (k + 1)! = (k + 1) * (k)! := Nat.factorial_succ k
  have hLHS : ENNReal.ofReal (1/((k:ℝ)+1)) * (((k)! : ℕ) : ℝ≥0∞)⁻¹
      = ENNReal.ofReal ((1/((k:ℝ)+1)) * (((k)!:ℝ))⁻¹) := by
    rw [← ENNReal.ofReal_natCast ((k)!),
      ← ENNReal.ofReal_inv_of_pos hfac,
      ← ENNReal.ofReal_mul (one_div_nonneg.mpr hk1.le)]
  have hRHS : ((k + 1 : ℕ) : ℝ≥0∞) * (((k)! : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal (((k:ℝ)+1) * ((k)!:ℝ)) := by
    rw [← ENNReal.ofReal_natCast (k + 1), ← ENNReal.ofReal_natCast ((k)!),
      ← ENNReal.ofReal_mul (show (0:ℝ) ≤ ((k + 1 : ℕ):ℝ) from by positivity)]
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
  rw [hfacrw, Nat.cast_mul, hLHS, hRHS,
    ← ENNReal.ofReal_inv_of_pos (mul_pos hk1 hfac)]
  congr 1
  rw [one_div, mul_inv]

/-- Closed form: the coordinate simplex has volume `1 / k!`. -/
public theorem volume_stdSimplexPi (k : ℕ) :
    volume (stdSimplexPi k) = ((k ! : ℕ) : ℝ≥0∞)⁻¹ := by
  induction k with
  | zero =>
    rw [volume_stdSimplexPi_zero]
    simp
  | succ k IH =>
    exact volume_stdSimplexPi_succ k IH

/-- Difference matrix: row `s` holds the coordinates of `v s.succ - v 0`. -/
@[expose] public noncomputable def diffMatrix {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun s t => v s.succ t - v 0 t

/-- Partially reduced `simDet` matrix: for `s ∈ S`, row `s.succ` has row `0`
subtracted. `S = ∅` recovers the `simDet` matrix. -/
@[expose] public noncomputable def redMatrix {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) (S : Finset (Fin k)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun r c =>
    if ∃ s ∈ S, r = s.succ
    then Fin.cases (1 : ℝ) (fun j => v r j) c
      - Fin.cases (1 : ℝ) (fun j => v 0 j) c
    else Fin.cases (1 : ℝ) (fun j => v r j) c

public theorem det_redMatrix_empty {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Matrix.det (redMatrix v ∅) = simDet v := by
  simp only [simDet]
  congr 1
  ext r c
  simp only [redMatrix, Matrix.of_apply]
  have hn : ¬ ∃ s ∈ (∅ : Finset (Fin k)), r = s.succ := by
    rintro ⟨s, hs, _⟩
    exact Finset.notMem_empty s hs
  rw [ite_eq_right hn]

public theorem redMatrix_insert {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k))
    {S : Finset (Fin k)} {s : Fin k} (hs : s ∉ S) :
    redMatrix v (insert s S)
      = Matrix.updateRow (redMatrix v S) s.succ
        ((redMatrix v S) s.succ - (redMatrix v S) 0) := by
  ext r c
  simp only [redMatrix, Matrix.of_apply]
  by_cases hr : r = s.succ
  · subst hr
    simp only [Matrix.updateRow_self, Pi.sub_apply, Matrix.of_apply]
    have hL : ∃ t ∈ insert s S, s.succ = t.succ :=
      ⟨s, Finset.mem_insert_self s S, rfl⟩
    rw [ite_eq_left hL]
    have h1 : ¬ ∃ t ∈ S, s.succ = t.succ := by
      rintro ⟨t, htS, hst⟩
      have hts : t = s := Fin.succ_injective k hst.symm
      subst hts
      exact hs htS
    have h2 : ¬ ∃ t ∈ S, (0 : Fin (k + 1)) = t.succ := by
      rintro ⟨t, _, h0⟩
      exact (by simp : t.succ ≠ 0) h0.symm
    rw [ite_eq_right h1, ite_eq_right h2]
  · rw [Matrix.updateRow_ne hr]
    simp only [Matrix.of_apply]
    by_cases hQ : ∃ t ∈ S, r = t.succ
    · have hP : ∃ t ∈ insert s S, r = t.succ := by
        obtain ⟨t, htS, hrt⟩ := hQ
        exact ⟨t, Finset.mem_insert_of_mem htS, hrt⟩
      rw [ite_eq_left hP, ite_eq_left hQ]
    · have hP : ¬ ∃ t ∈ insert s S, r = t.succ := by
        rintro ⟨t, ht, hrt⟩
        rw [Finset.mem_insert] at ht
        obtain rfl | ht := ht
        · exact hr hrt
        · exact hQ ⟨t, ht, hrt⟩
      rw [ite_eq_right hP, ite_eq_right hQ]

public theorem det_redMatrix_insert {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k))
    {S : Finset (Fin k)} {s : Fin k} (hs : s ∉ S) :
    Matrix.det (redMatrix v (insert s S))
      = Matrix.det (redMatrix v S) := by
  rw [redMatrix_insert v hs]
  have hsub : (redMatrix v S) s.succ - (redMatrix v S) 0
      = (redMatrix v S) s.succ + (-1 : ℝ) • (redMatrix v S) 0 := by
    rw [sub_eq_add_neg]
    congr 1
    simp
  rw [hsub, Matrix.det_updateRow_add_smul_self _ (by simp : s.succ ≠ 0) (-1)]

public theorem det_redMatrix {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) (S : Finset (Fin k)) :
    Matrix.det (redMatrix v S) = simDet v := by
  induction S using Finset.induction with
  | empty => exact det_redMatrix_empty v
  | insert a s ha ih => rw [det_redMatrix_insert v ha, ih]

/-- Fully reduced matrix: row `0` kept, all other rows have row `0` subtracted. -/
@[expose] public noncomputable def redMatrixFull {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun r c =>
    if r = 0 then Fin.cases (1 : ℝ) (fun j => v r j) c
    else Fin.cases (1 : ℝ) (fun j => v r j) c
      - Fin.cases (1 : ℝ) (fun j => v 0 j) c

public theorem redMatrix_univ {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    redMatrix v Finset.univ = redMatrixFull v := by
  ext r c
  simp only [redMatrix, redMatrixFull, Matrix.of_apply]
  by_cases hr : r = 0
  · rw [ite_eq_left hr]
    have hn : ¬ ∃ s ∈ (Finset.univ : Finset (Fin k)), r = s.succ := by
      rintro ⟨s, _, h0⟩
      exact (by simp : s.succ ≠ 0) (h0.symm.trans hr)
    rw [ite_eq_right hn]
  · rw [ite_eq_right hr]
    have hP : ∃ s ∈ (Finset.univ : Finset (Fin k)), r = s.succ := by
      obtain ⟨s, hs⟩ := Fin.exists_succ_eq_of_ne_zero hr
      exact ⟨s, Finset.mem_univ s, hs.symm⟩
    rw [ite_eq_left hP]

public theorem det_redMatrixFull {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Matrix.det (redMatrixFull v) = Matrix.det (diffMatrix v) := by
  have hB00 : redMatrixFull v 0 0 = 1 := by
    simp [redMatrixFull, Matrix.of_apply]
  have hsub : Matrix.submatrix (redMatrixFull v) (0 : Fin (k + 1)).succAbove
      (0 : Fin (k + 1)).succAbove = diffMatrix v := by
    ext s t
    simp only [Matrix.submatrix_apply, Fin.succAbove_zero, redMatrixFull,
      diffMatrix, Matrix.of_apply]
    rw [ite_eq_right (by simp : s.succ ≠ 0)]
    simp only [Fin.cases_succ]
  rw [Matrix.det_succ_column _ 0, Finset.sum_eq_single (0 : Fin (k + 1))]
  · rw [hB00, hsub]
    simp
  · intro i _ hi0
    have hBi0 : redMatrixFull v i 0 = 0 := by
      simp only [redMatrixFull, Matrix.of_apply]
      rw [ite_eq_right hi0]
      simp
    simp [hBi0]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- The `simDet` determinant equals the determinant of the difference matrix
(row operations + cofactor expansion along the leading column). -/
public theorem simDet_eq_det_diffMatrix {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    simDet v = Matrix.det (diffMatrix v) := by
  rw [← det_redMatrixFull v, ← redMatrix_univ v]
  exact (det_redMatrix v Finset.univ).symm

/-- Linear part on the coordinate space. -/
@[expose] public noncomputable def diffLin {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  Matrix.mulVecLin (Matrix.transpose (diffMatrix v))

/-- Coordinate inclusion as a linear map (coercion is `toLp 2`). -/
@[expose] public noncomputable def toEuclidLin (k : ℕ) :
    (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm.toLinearMap

/-- Full linear part into Euclidean space. -/
@[expose] public noncomputable def simLin {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  toEuclidLin k ∘ₗ diffLin v

/-- Affine parametrization of the simplex. -/
@[expose] public noncomputable def simAffine {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    (Fin k → ℝ) → EuclideanSpace ℝ (Fin k) :=
  fun u => v 0 + simLin v u

public theorem toEuclidLin_apply {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    toEuclidLin k (fun i => x i) = x :=
  ContinuousLinearEquiv.symm_apply_apply (EuclideanSpace.equiv (Fin k) ℝ) x

public theorem simLin_apply {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) (u : Fin k → ℝ) :
    simLin v u = ∑ j, u j • (v j.succ - v 0) := by
  have h1 : Matrix.mulVec (Matrix.transpose (diffMatrix v)) u
      = ∑ j, u j • (fun i => diffMatrix v j i) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : toEuclidLin k (∑ j, u j • (fun i => diffMatrix v j i))
      = ∑ j, u j • (v j.succ - v 0) := by
    rw [_root_.map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hw : (fun i => diffMatrix v j i)
        = (fun i => (v j.succ - v 0) i) := by
      funext i
      simp [diffMatrix]
    rw [hw, map_smul, toEuclidLin_apply]
  simp only [simLin, diffLin, LinearMap.comp_apply, Matrix.mulVecLin_apply]
  rw [h1, h2]

/-- Determinant of the coordinate linear part. -/
public theorem det_diffLin {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    LinearMap.det (diffLin v) = Matrix.det (diffMatrix v) := by
  simp only [diffLin, det_mulVecLin, Matrix.det_transpose]

/-- The coordinate inclusion is measure-preserving (`PiLp` bridge). -/
public theorem measurePreserving_toEuclidLin (k : ℕ) :
    MeasurePreserving (toEuclidLin k) volume volume :=
  PiLp.volume_preserving_toLp (Fin k)

/-- Volume is preserved under the coordinate inclusion. -/
public theorem volume_toEuclidLin_image (k : ℕ) (s : Set (Fin k → ℝ)) :
    volume (toEuclidLin k '' s) = volume s := by
  have hfun : ⇑(toEuclidLin k)
      = ⇑((MeasurableEquiv.toLp 2 (Fin k → ℝ)).toEquiv) := rfl
  rw [hfun, Equiv.image_eq_preimage_symm]
  exact MeasurePreserving.measure_preimage_equiv
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k)) s

/-- Continuity of the simplex linear part. -/
public theorem continuous_simLin {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Continuous (simLin v) :=
  (simLin v).continuous_of_finiteDimensional

/-- Measurability of the simplex linear part. -/
public theorem measurable_simLin {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Measurable (simLin v) :=
  (continuous_simLin v).measurable

/-- Continuity of the affine parametrization. -/
public theorem continuous_simAffine {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Continuous (simAffine v) := by
  show Continuous fun u => v 0 + simLin v u
  exact continuous_const.add (continuous_simLin v)

/-- Measurability of the affine parametrization. -/
public theorem measurable_simAffine {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Measurable (simAffine v) :=
  (continuous_simAffine v).measurable

/-- Volume scaling of the coordinate linear part, in terms of `simDet`. -/
public theorem volume_diffLin_image {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) (s : Set (Fin k → ℝ)) :
    volume (diffLin v '' s) = ENNReal.ofReal |simDet v| * volume s := by
  rw [addHaar_image_linearMap, det_diffLin, ← simDet_eq_det_diffMatrix]

/-- Volume scaling of the full simplex linear part. -/
public theorem volume_simLin_image {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) (s : Set (Fin k → ℝ)) :
    volume (simLin v '' s) = ENNReal.ofReal |simDet v| * volume s := by
  have hcomp : ⇑(simLin v)
      = fun x => ⇑(toEuclidLin k) (⇑(diffLin v) x) := rfl
  have himg : ⇑(simLin v) '' s = ⇑(toEuclidLin k) '' (⇑(diffLin v) '' s) := by
    rw [hcomp]
    exact (Set.image_image _ _ _).symm
  rw [himg, volume_toEuclidLin_image, volume_diffLin_image]

/-- Translation invariance: the affine image has the same volume as the linear image. -/
public theorem volume_simAffine_image {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) (s : Set (Fin k → ℝ)) :
    volume (simAffine v '' s) = volume (simLin v '' s) := by
  have hcomp : simAffine v
      = fun x => (fun y => v 0 + y) (⇑(simLin v) x) := rfl
  have he : (fun y => v 0 + y) = ⇑(Equiv.addLeft (v 0)) := rfl
  have himg : simAffine v '' s = (fun y => v 0 + y) '' (⇑(simLin v) '' s) := by
    rw [hcomp]
    exact (Set.image_image _ _ _).symm
  rw [himg, he, Equiv.image_eq_preimage_symm]
  show volume ((fun h => -(v 0) + h) ⁻¹' (⇑(simLin v) '' s)) = volume (⇑(simLin v) '' s)
  exact measure_preimage_add volume (-(v 0)) _

/-- The coordinate simplex is compact (closed + bounded in finite dimensions). -/
public theorem isCompact_stdSimplexPi (k : ℕ) : IsCompact (stdSimplexPi k) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have h1 : ∀ j : Fin k, IsClosed {u : Fin k → ℝ | 0 ≤ u j} := fun j =>
      isClosed_le continuous_const (continuous_apply j)
    have h2 : IsClosed {u : Fin k → ℝ | ∑ j, u j ≤ 1} :=
      isClosed_le
        (continuous_finsetSum _ (fun j _ => continuous_apply j)) continuous_const
    have hset : stdSimplexPi k
        = (⋂ j, {u : Fin k → ℝ | 0 ≤ u j}) ∩ {u | ∑ j, u j ≤ 1} := by
      ext u
      simp [stdSimplexPi, Set.mem_iInter]
    rw [hset]
    exact (isClosed_iInter h1).inter h2
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1, fun u hu => ?_⟩
    have hu' : (∀ j, 0 ≤ u j) ∧ ∑ j, u j ≤ 1 := hu
    obtain ⟨hupos, husum⟩ := hu'
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    have hle : u j ≤ ∑ i, u i :=
      Finset.single_le_sum (fun i _ => hupos i) (Finset.mem_univ j)
    rw [Real.norm_eq_abs, abs_of_nonneg (hupos j)]
    linarith

/-- The coordinate simplex is closed. -/
public theorem isClosed_stdSimplexPi (k : ℕ) : IsClosed (stdSimplexPi k) :=
  (isCompact_stdSimplexPi k).isClosed

/-- Main affine-image identity: `|simDet| = k! * vol` of the affine simplex image. -/
public theorem abs_simDet_eq_volume_image {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    ENNReal.ofReal |simDet v|
      = ((k ! : ℕ) : ℝ≥0∞) * volume (simAffine v '' stdSimplexPi k) := by
  have hk0 : ((k ! : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hkTop : ((k ! : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [volume_simAffine_image, volume_simLin_image, volume_stdSimplexPi,
    ← mul_assoc, mul_comm ((k ! : ℕ) : ℝ≥0∞), mul_assoc,
    ENNReal.mul_inv_cancel hk0 hkTop, mul_one]

/-- The coordinate simplex is convex. -/
public theorem convex_stdSimplexPi (k : ℕ) : Convex ℝ (stdSimplexPi k) := by
  intro u hu w hw a b ha hb hab
  have hu' : (∀ j, 0 ≤ u j) ∧ ∑ j, u j ≤ 1 := hu
  have hw' : (∀ j, 0 ≤ w j) ∧ ∑ j, w j ≤ 1 := hw
  obtain ⟨hupos, husum⟩ := hu'
  obtain ⟨hwpos, hwsum⟩ := hw'
  show (∀ j, 0 ≤ (a • u + b • w) j) ∧ ∑ j, (a • u + b • w) j ≤ 1
  constructor
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hupos j)) (mul_nonneg hb (hwpos j))
  · have hsum : ∑ j, (a • u + b • w) j = a * ∑ j, u j + b * ∑ j, w j := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
    rw [hsum]
    calc a * ∑ j, u j + b * ∑ j, w j ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left husum ha)
              (mul_le_mul_of_nonneg_left hwsum hb)
        _ = 1 := by rw [mul_one, mul_one, hab]

/-- Every vertex lies in the affine image of the coordinate simplex. -/
public theorem range_subset_simAffine_image {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Set.range v ⊆ simAffine v '' stdSimplexPi k := by
  intro y hy
  obtain ⟨i, rfl⟩ := hy
  by_cases hi : i = 0
  · subst hi
    refine ⟨0, ?_, ?_⟩
    · show (∀ j, 0 ≤ (0 : Fin k → ℝ) j) ∧ ∑ j, (0 : Fin k → ℝ) j ≤ 1
      simp
    · show v 0 + simLin v 0 = v 0
      rw [map_zero, add_zero]
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    set e : Fin k → ℝ := Pi.single j 1 with he
    refine ⟨e, ?_, ?_⟩
    · show (∀ t, 0 ≤ e t) ∧ ∑ t, e t ≤ 1
      constructor
      · intro t
        by_cases ht : t = j
        · subst ht
          simp [he]
        · simp [he, ht]
      · have h0 : ∀ t ∈ (Finset.univ : Finset (Fin k)), t ≠ j → e t = 0 :=
          fun t _ htj => by simp [he, htj]
        have h2 : j ∉ (Finset.univ : Finset (Fin k)) → e j = 0 :=
          fun hj => absurd (Finset.mem_univ j) hj
        rw [Finset.sum_eq_single j h0 h2]
        simp [he]
    · show v 0 + simLin v e = v j.succ
      rw [simLin_apply]
      have h0 : ∀ t ∈ (Finset.univ : Finset (Fin k)),
          t ≠ j → e t • (v t.succ - v 0) = 0 := by
        intro t _ htj
        have h : e t = 0 := by simp [he, htj]
        rw [h, zero_smul]
      have h2 : j ∉ (Finset.univ : Finset (Fin k)) →
          e j • (v j.succ - v 0) = 0 :=
        fun hj => absurd (Finset.mem_univ j) hj
      rw [Finset.sum_eq_single j h0 h2]
      have hs : e j = 1 := by simp [he]
      rw [hs, one_smul]
      exact add_sub_cancel _ _

/-- The affine image of the coordinate simplex is convex. -/
public theorem convex_simAffine_image {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    Convex ℝ (simAffine v '' stdSimplexPi k) := by
  intro y1 hy1 y2 hy2 a b ha hb hab
  obtain ⟨u1, hu1, rfl⟩ := hy1
  obtain ⟨u2, hu2, rfl⟩ := hy2
  have hmem : a • u1 + b • u2 ∈ stdSimplexPi k :=
    convex_stdSimplexPi k hu1 hu2 ha hb hab
  refine ⟨a • u1 + b • u2, hmem, ?_⟩
  show simAffine v (a • u1 + b • u2)
      = a • simAffine v u1 + b • simAffine v u2
  show v 0 + simLin v (a • u1 + b • u2)
      = a • (v 0 + simLin v u1) + b • (v 0 + simLin v u2)
  rw [map_add, map_smul, map_smul]
  have h : a • (v 0 + simLin v u1) + b • (v 0 + simLin v u2)
      = (a + b) • v 0 + (a • simLin v u1 + b • simLin v u2) := by
    rw [smul_add, smul_add, add_smul]
    abel
  rw [h, hab, one_smul]

/-- The affine image lies in the convex hull of the vertices. -/
public theorem simAffine_image_subset_convexHull {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    simAffine v '' stdSimplexPi k ⊆ convexHull ℝ (Set.range v) := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := hy
  have hu' : (∀ j, 0 ≤ u j) ∧ ∑ j, u j ≤ 1 := hu
  obtain ⟨hupos, husum⟩ := hu'
  set w : Fin (k + 1) → ℝ := Fin.cases (1 - ∑ j, u j) u with hw
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))), 0 ≤ w i := by
    intro i _
    refine Fin.cases ?_ ?_ i
    · simp only [hw, Fin.cases_zero]
      linarith
    · intro j
      simp only [hw, Fin.cases_succ]
      exact hupos j
  have hwsum : ∑ i, w i = 1 := by
    have hS : ∑ i : Fin k, w i.succ = ∑ j, u j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [hw, Fin.cases_succ]
    rw [Fin.sum_univ_succ, hS]
    simp only [hw, Fin.cases_zero]
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
      v i ∈ convexHull ℝ (Set.range v) :=
    fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i)
  have hcc := (convex_convexHull ℝ (Set.range v)).sum_mem hwpos hwsum hz
  have hsim : simAffine v u = ∑ i, w i • v i := by
    have hsplit : ∑ i, w i • v i
        = w 0 • v 0 + ∑ j : Fin k, w j.succ • v j.succ :=
      Fin.sum_univ_succ (fun i => w i • v i)
    rw [hsplit]
    simp only [hw, Fin.cases_zero, Fin.cases_succ]
    show v 0 + simLin v u
        = (1 - ∑ j, u j) • v 0 + ∑ j, u j • v j.succ
    rw [simLin_apply]
    have hexpand : ∑ j, u j • (v j.succ - v 0)
        = (∑ j, u j • v j.succ) - (∑ j, u j) • v 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [hexpand]
    have hfin : v 0 + ((∑ j, u j • v j.succ) - (∑ j, u j) • v 0)
        = (1 - ∑ j, u j) • v 0 + ∑ j, u j • v j.succ := by
      rw [sub_smul, one_smul]
      abel
    exact hfin
  rw [hsim]
  exact hcc

/-- The convex hull of the vertices equals the affine image. -/
public theorem convexHull_range_eq_image {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    convexHull ℝ (Set.range v) = simAffine v '' stdSimplexPi k :=
  le_antisymm
    (convexHull_min (range_subset_simAffine_image v) (convex_simAffine_image v))
    (simAffine_image_subset_convexHull v)

/-- HI-SIMPVOL main identity: `|simDet| = k! * vol(convexHull)`. -/
public theorem abs_simDet_eq_volume_convexHull {k : ℕ}
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    ENNReal.ofReal |simDet v|
      = ((k ! : ℕ) : ℝ≥0∞) * volume (convexHull ℝ (Set.range v)) := by
  rw [convexHull_range_eq_image]
  exact abs_simDet_eq_volume_image v

end HypercubeInequality
