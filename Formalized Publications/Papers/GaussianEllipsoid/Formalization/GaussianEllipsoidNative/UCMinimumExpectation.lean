import UCProjectedNorm

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace UCEscape

/-- A finite family of projected Gaussian norms, minimized pointwise. -/
def projectedNormMinimum {J : Type*} [Fintype J] [Nonempty J] (n r : ℕ)
    (U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(U j).toContinuousLinearMap.adjoint x‖)

theorem projectedNormMinimum_nonneg {J : Type*} [Fintype J] [Nonempty J]
    (n r : ℕ) (U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ projectedNormMinimum n r U x := by
  exact Finset.le_inf' _ _ (fun j _ => norm_nonneg _)

theorem projectedNormMinimum_continuous {J : Type*} [Fintype J] [Nonempty J]
    (n r : ℕ) (U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Continuous (projectedNormMinimum n r U) := by
  exact Continuous.finset_inf'_apply _ (fun j _ => by fun_prop)

theorem projectedNormMinimum_integrable {J : Type*} [Fintype J] [Nonempty J]
    (n r : ℕ) (U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Integrable (projectedNormMinimum n r U) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  classical
  let j : J := Classical.choice inferInstance
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖(U j).toContinuousLinearMap.adjoint x‖) (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ((U j).toContinuousLinearMap.adjoint.integrable_comp IsGaussian.integrable_id).norm
  apply hi.mono' (projectedNormMinimum_continuous n r U).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (projectedNormMinimum_nonneg n r U x)]
    exact Finset.inf'_le _ (Finset.mem_univ j)

/-- The lower-tail union bound is valid for arbitrary dependent orthonormal frames. -/
theorem projectedNormMinimum_lower_tail {J : Type*} [Fintype J] [Nonempty J]
    (n r : ℕ) (U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x | projectedNormMinimum n r U x ≤ (1 - ε) * Real.sqrt r} ≤
      (Fintype.card J : ℝ) * Real.exp (-ε ^ 2 * (r : ℝ) / 8) := by
  classical
  have heq : {x | projectedNormMinimum n r U x ≤ (1 - ε) * Real.sqrt r} =
      ⋃ j : J, {x | ‖(U j).toContinuousLinearMap.adjoint x‖ ≤
        (1 - ε) * Real.sqrt r} := by
    ext x
    simp [projectedNormMinimum, Finset.inf'_le_iff]
  rw [heq]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ j : J, Real.exp (-ε ^ 2 * (r : ℝ) / 8) :=
      Finset.sum_le_sum fun j _ => projected_norm_lower_tail n r (U j) ε hε hε1
    _ = _ := by simp

/-- Integrating a nonnegative random variable on its good event gives this elementary
one-sided expectation lower bound. -/
theorem integral_ge_threshold_mul_one_sub_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ)
    (hf : Integrable f μ) (hm : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (a p : ℝ) (ha : 0 ≤ a) (ht : μ.real {x | f x ≤ a} ≤ p) :
    a * (1 - p) ≤ ∫ x, f x ∂μ := by
  let B : Set X := {x | f x ≤ a}
  have hB : MeasurableSet B := measurableSet_le hm measurable_const
  have hl : ∫ x, Bᶜ.indicator (fun _ => a) x ∂μ ≤ ∫ x, f x ∂μ := by
    apply integral_mono ((integrable_const a).indicator hB.compl) hf
    intro x
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_notMem (show x ∉ Bᶜ from fun h => h hx)]
      exact hpos x
    · rw [Set.indicator_of_mem (show x ∈ Bᶜ from hx)]
      exact le_of_lt (lt_of_not_ge hx)
  rw [integral_indicator_const _ hB.compl, smul_eq_mul,
    measureReal_compl hB, probReal_univ] at hl
  calc
    a * (1 - p) ≤ (1 - μ.real B) * a := by nlinarith
    _ ≤ _ := hl

/-- Actual Gaussian expectation of the minimum of any finite nonempty family of
rank-r orthonormal-frame projection norms. No independence between frames is assumed. -/
theorem projectedNormMinimum_expectation_lower {J : Type*} [Fintype J] [Nonempty J]
    (n r : ℕ) (U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) * Real.sqrt r *
        (1 - (Fintype.card J : ℝ) * Real.exp (-ε ^ 2 * (r : ℝ) / 8)) ≤
      ∫ x, projectedNormMinimum n r U x ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  apply integral_ge_threshold_mul_one_sub_tail _ _
    (projectedNormMinimum_integrable n r U)
    (projectedNormMinimum_continuous n r U).measurable
    (projectedNormMinimum_nonneg n r U) _ _ (by positivity)
  exact projectedNormMinimum_lower_tail n r U ε hε hε1

/-- Entropy-form lower bound for a finite family whose size is at most exp H. -/
theorem projectedNormMinimum_expectation_lower_of_card_le_exp
    {J : Type*} [Fintype J] [Nonempty J]
    (n r : ℕ) (U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ε H : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp H) :
    (1 - ε) * Real.sqrt r * (1 - Real.exp (H - ε ^ 2 * (r : ℝ) / 8)) ≤
      ∫ x, projectedNormMinimum n r U x ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  apply le_trans _ (projectedNormMinimum_expectation_lower n r U ε hε hε1)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sub_le_sub_left
  calc
    (Fintype.card J : ℝ) * Real.exp (-ε ^ 2 * (r : ℝ) / 8) ≤
        Real.exp H * Real.exp (-ε ^ 2 * (r : ℝ) / 8) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = Real.exp (H - ε ^ 2 * (r : ℝ) / 8) := by
      rw [← Real.exp_add]; congr 1; ring

/-- A convenient near-full-rank mean bound when the total exceptional probability
is at most the chosen relative error. -/
theorem projectedNormMinimum_expectation_near_sqrt
    {J : Type*} [Fintype J] [Nonempty J]
    (n r : ℕ) (U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (htail : (Fintype.card J : ℝ) * Real.exp (-ε ^ 2 * (r : ℝ) / 8) ≤ ε) :
    (1 - 2 * ε) * Real.sqrt r ≤
      ∫ x, projectedNormMinimum n r U x ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  apply le_trans _ (projectedNormMinimum_expectation_lower n r U ε hε hε1)
  have hs : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hm : (1 - ε) * Real.sqrt r * (1 - ε) ≤
      (1 - ε) * Real.sqrt r *
        (1 - (Fintype.card J : ℝ) * Real.exp (-ε ^ 2 * (r : ℝ) / 8)) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left htail 1) (by positivity)
  have hp := mul_nonneg (sq_nonneg ε) hs
  nlinarith

/-- The same actual expectation lower bound under the project's coordinate realization. -/
theorem euclideanGaussian_projectedNormMinimum_expectation_lower
    {J : Type*} [Fintype J] [Nonempty J]
    (n r : ℕ) (U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) * Real.sqrt r *
        (1 - (Fintype.card J : ℝ) * Real.exp (-ε ^ 2 * (r : ℝ) / 8)) ≤
      ∫ x, projectedNormMinimum n r U x
        ∂GaussianMixedNormHelpers.euclideanGaussianLaw (Fin n) := by
  rw [euclideanGaussianLaw_eq_stdGaussian]
  exact projectedNormMinimum_expectation_lower n r U ε hε hε1

#print axioms projectedNormMinimum_expectation_lower
#print axioms projectedNormMinimum_expectation_lower_of_card_le_exp
#print axioms projectedNormMinimum_expectation_near_sqrt
#print axioms euclideanGaussian_projectedNormMinimum_expectation_lower
end UCEscape
