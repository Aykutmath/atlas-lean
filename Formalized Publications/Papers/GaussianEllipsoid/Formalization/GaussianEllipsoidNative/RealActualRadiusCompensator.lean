import RealRowGroupVariance
import RealMartingaleRadius

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable
open Finset MeasureTheory GaussianEllipsoid GaussianEllipsoid.PaperCanonicalPolar
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoidCandidate

/-- The literal maximum radius is nonnegative, including an empty future. -/
theorem realPostprefixMGFRadius_nonneg {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ) (d : ℝ) :
    0 ≤ realPostprefixMGFRadius u amp groups T p d := by
  unfold realPostprefixMGFRadius
  split_ifs with hs
  · obtain ⟨j,hj⟩ := hs
    exact (div_nonneg (norm_nonneg (realDyadicGroupVector u amp groups T j)) (Real.sqrt_nonneg d)).trans
      (Finset.le_sup' (fun r : ℕ => ‖realDyadicGroupVector u amp groups T r‖/Real.sqrt d) hj)
  · exact le_rfl

/-- Every actual group radius is bounded by the literal finite maximum. -/
theorem real_group_radius_le_actual_max {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p j : ℕ) (d : ℝ)
    (hpj : p ≤ j) (hj : j < groups.length) :
    ‖realDyadicGroupVector u amp groups T j‖/Real.sqrt d ≤
      realPostprefixMGFRadius u amp groups T p d := by
  rw [realPostprefixMGFRadius_eq_max u amp groups T p d (hpj.trans_lt hj)]
  exact Finset.le_sup' (fun r : ℕ => ‖realDyadicGroupVector u amp groups T r‖/Real.sqrt d)
    (mem_Ico.mpr ⟨hpj,hj⟩)

/-- B_mart bounds each literal normalized postprefix coefficient; no independent
coefficient envelope is supplied. This also covers zero coordinates and empty futures. -/
theorem real_postprefix_normalized_coefficient_le_radius {n : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ) (d : ℝ)
    (i : Fin n) :
    |postprefixCoefficients u amp groups T p i/Real.sqrt d| ≤
      realPostprefixMGFRadius u amp groups T p d := by
  rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg d)]
  by_cases hi : i ∈ postprefixSupport u amp groups T p
  · have hi' := hi
    rw [postprefixSupport_eq_biUnion] at hi'
    obtain ⟨j,hj,hij⟩ := mem_biUnion.mp hi'
    have hn : |u i| ≤ ‖realDyadicGroupVector u amp groups T j‖ := by
      simpa only [realDyadicGroupVector,hij,ite_true,Real.norm_eq_abs] using
        norm_le_pi_norm (realDyadicGroupVector u amp groups T j) i
    simp only [postprefixCoefficients,hi,ite_true]
    exact (div_le_div_of_nonneg_right hn (Real.sqrt_nonneg d)).trans
      (real_group_radius_le_actual_max u amp groups T p j d (mem_Ico.mp hj).1 (mem_Ico.mp hj).2)
  · simp only [postprefixCoefficients,hi,ite_false,abs_zero,zero_div]
    exact realPostprefixMGFRadius_nonneg u amp groups T p d

/-- Zero actual maximum means the entire normalized cross vector is zero. -/
theorem real_normalized_postprefix_eq_zero_of_radius_zero {n : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ) (d : ℝ)
    (hB : realPostprefixMGFRadius u amp groups T p d=0) :
    (fun i => postprefixCoefficients u amp groups T p i/Real.sqrt d) = 0 := by
  funext i
  have h := real_postprefix_normalized_coefficient_le_radius u amp groups T p d i
  rw [hB] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- The literal group compensated expectation with the exact source maximum
B_mart and lambda <= 1/(sqrt(2)*B_mart), with the coefficient-domain premise discharged. -/
theorem real_actual_group_compensator_actual_radius {n r q : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hB : 0 < realPostprefixMGFRadius u amp groups T p d)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hlamB : lam ≤ 1/(Real.sqrt 2*realPostprefixMGFRadius u amp groups T p d)) :
    let G := dyadicGroupSupport u amp groups T
    let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
    let U := real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat
    let v := fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d
    let Xg := fun X : Fin n → Euclid q × Euclid r =>
      ∑ j ∈ Ico p groups.length,
        ⟪operatorFrobenius (exactCompletedPrefix U (capturedBlockLo G p b)
            (capturedBlockHi G p b) (permuteRows e X) (supportCut G j)),
          operatorFrobenius (bilinearSynthesis (fun i => if i∈G j then u i/Real.sqrt d else 0) X)⟫_ℝ
    let Vg := fun X : Fin n → Euclid q × Euclid r =>
      ∑ j ∈ Ico p groups.length,(∑ i ∈ G j,(u i)^2)*
        ‖operatorFrobenius (exactCompletedPrefix U (capturedBlockLo G p b)
          (capturedBlockHi G p b) (permuteRows e X) (supportCut G j))‖^2/(d:ℝ)
    Integrable (fun X : Fin n → Euclid q × Euclid r =>
      Real.exp (-lam*Xg X-lam^2*Vg X))
        (gaussianBilinearSampleLaw (Fin n) q r) ∧
    (∫ X : Fin n → Euclid q × Euclid r,
      Real.exp (-lam*Xg X-lam^2*Vg X)
        ∂gaussianBilinearSampleLaw (Fin n) q r)≤1 := by
  apply real_actual_group_compensator ratio u amp ha groups T d p b hreg hflat
    (realPostprefixMGFRadius u amp groups T p d) hB ?_ lam hlam hlamB
  intro i
  exact real_postprefix_normalized_coefficient_le_radius u amp groups T p d
    ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat).symm i)

/-- If the exact B_mart is zero, the compensated exponential is identically one
for every lambda. No positive-radius assumption or reciprocal at zero is used. -/
theorem real_actual_group_compensator_radius_zero {n r q : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hB : realPostprefixMGFRadius u amp groups T p d=0) (lam : ℝ) :
    let G := dyadicGroupSupport u amp groups T
    let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
    let U := real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat
    let v := fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d
    Integrable (fun X : Fin n → Euclid q × Euclid r =>
      Real.exp (-lam*capturedExactCross G p b U v (permuteRows e X)-
        lam^2*realActualExactCapturedVariance ratio u amp ha groups T d p b hreg hflat X))
      (gaussianBilinearSampleLaw (Fin n) q r) ∧
    (∫ X : Fin n → Euclid q × Euclid r,
      Real.exp (-lam*capturedExactCross G p b U v (permuteRows e X)-
        lam^2*realActualExactCapturedVariance ratio u amp ha groups T d p b hreg hflat X)
        ∂gaussianBilinearSampleLaw (Fin n) q r)=1 := by
  have hz := real_normalized_postprefix_eq_zero_of_radius_zero u amp groups T p d hB
  have hv (i : Fin n) : postprefixCoefficients u amp groups T p i/Real.sqrt d=0 :=
    congrFun hz i
  simp only [capturedExactCross,exactPrefixCross,realActualExactCapturedVariance,exactPrefixVariance]
  simp [hv]

#print axioms realPostprefixMGFRadius_nonneg
#print axioms real_group_radius_le_actual_max
#print axioms real_postprefix_normalized_coefficient_le_radius
#print axioms real_normalized_postprefix_eq_zero_of_radius_zero
#print axioms real_actual_group_compensator_actual_radius
#print axioms real_actual_group_compensator_radius_zero
end GaussianEllipsoidCandidate
