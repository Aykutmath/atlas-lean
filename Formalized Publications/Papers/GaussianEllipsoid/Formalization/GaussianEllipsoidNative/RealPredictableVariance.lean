import PrefixWitnessRankEnergy
import RealDyadicPaper
import PaperExactPrefixPolar

noncomputable section
set_option maxHeartbeats 600000
open Finset Module GaussianEllipsoid GaussianMixedNormHelpers
open scoped BigOperators
namespace GaussianEllipsoid
/-- Every contraction with the actual right-prefix support has rank-sensitive
Frobenius energy, independently of how the polar witness was selected. -/
theorem prefix_supported_contraction_energy {n r q : ℕ}
    (X : Fin n → Euclid q × Euclid r) (t : ℕ) (W : Euclid q →L[ℝ] Euclid r)
    (hW : ‖W‖ ≤ 1) (hsupport : W ∘L rightPrefixProjector X t = W) :
    ‖operatorFrobenius W‖^2 ≤ (t:ℝ) := by
  have h := frobenius_supported_contraction_sq_le_rank W (rightPrefixProjector X t)
    hW (prefixSpanProjector_selfAdjoint _ t)
    (prefixSpanProjector_comp_of_le _ (le_refl t)) hsupport
  have hr : LinearMap.range (rightPrefixProjector X t).toLinearMap =
      Submodule.span ℝ ((fun i => (X i).1) '' {i : Fin n | i.val < t}) := by
    unfold rightPrefixProjector
    rw [prefixSpanProjector_eq]
    exact Submodule.range_starProjection _
  rw [hr] at h
  exact h.trans (by exact_mod_cast prefix_span_finrank_le (fun i => (X i).1) t)
end GaussianEllipsoid

namespace GaussianEllipsoidCandidate

/-- Rank-sensitive predictable variance for every real record growth ratio
greater than one and any contractive witnesses with the actual preceding-prefix
support. In particular this applies to canonical exact partial-polar witnesses. -/
theorem real_supported_group_predictable_variance_le {n r q : ℕ}
    (ratio : ℝ) (hratio : 1 < ratio) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio
      fun t => ((dyadicBin u amp t).card : ℝ)))
    (X : Fin n → Euclid q × Euclid r)
    (Z : ℕ → (Euclid q →L[ℝ] Euclid r))
    (hZ : ∀ j < groups.length, ‖Z j‖ ≤ 1)
    (hZsupport : ∀ j < groups.length,
      Z j ∘L rightPrefixProjector X (supportCut (dyadicGroupSupport u amp groups T) j) = Z j)
    (d : ℝ) (hd : 0 < d) :
    (∑ j ∈ range groups.length,
      (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2) *
        ‖operatorFrobenius (Z j)‖^2 / d) ≤
      (16*T*ratio^2/(3*(ratio-1)*d))*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  let C : ℝ := (T:ℝ)*ratio/(ratio-1)
  have hratio0 : 0 < ratio := by linarith
  have hden : 0 < ratio-1 := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm (j : ℕ) (hj : j ∈ range groups.length) :
      (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2) *
        ‖operatorFrobenius (Z j)‖^2 / d ≤
      (C*(16*ratio/3)/d)*(dyadicGroupMass u amp groups T j)^2 := by
    have henergy := prefix_supported_contraction_energy X
      (supportCut (dyadicGroupSupport u amp groups T) j) (Z j)
      (hZ j (mem_range.mp hj)) (hZsupport j (mem_range.mp hj))
    rw [actual_dyadic_supportCut_cast] at henergy
    have he := henergy.trans (real_actual_group_prefix_bounds ratio hratio u amp groups T hreg hchain j (mem_range.mp hj)).2
    have hprod := mul_le_mul_of_nonneg_left he
      (sum_nonneg (s := dyadicGroupSupport u amp groups T j) (fun i _ => sq_nonneg (u i)))
    have hQ := real_actual_group_energy_mass_product ratio u amp groups T hreg j (mem_range.mp hj)
    have hh := mul_le_mul_of_nonneg_left hQ hC
    have hbound : (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2) *
        ‖operatorFrobenius (Z j)‖^2 ≤
        C*(16*ratio/3)*(dyadicGroupMass u amp groups T j)^2 := by
      calc
        _ ≤ (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2) *
            (C*dyadicGroupScale u amp groups j) := hprod
        _ = C*((∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2)*
            dyadicGroupScale u amp groups j) := by ring
        _ ≤ C*((16*ratio/3)*(dyadicGroupMass u amp groups T j)^2) := hh
        _ = _ := by ring
    exact (div_le_div_of_nonneg_right hbound hd.le).trans_eq (by ring)
  calc
    _ ≤ ∑ j ∈ range groups.length, (C*(16*ratio/3)/d)*(dyadicGroupMass u amp groups T j)^2 :=
      sum_le_sum hterm
    _ = (C*(16*ratio/3)/d)*(∑ j ∈ range groups.length,(dyadicGroupMass u amp groups T j)^2) := by
      rw [Finset.mul_sum]
    _ ≤ (C*(16*ratio/3)/d)*(∑ j ∈ range groups.length,dyadicGroupMass u amp groups T j)^2 :=
      mul_le_mul_of_nonneg_left
        (sum_sq_le_sq_sum_of_nonneg (fun j _ => sum_nonneg (fun i _ => abs_nonneg (u i)))) (by positivity)
    _ = _ := by
      rw [← real_actual_group_mass_sum ratio u amp ha groups T hreg hflat]
      dsimp [C]
      field_simp [hd.ne',hden.ne'] <;> ring
/-- The source's rank-sensitive predictable-variance display for every real
record growth ratio greater than one. All witnesses are the actual measurable
completed polar-prefix witnesses. -/
theorem real_actual_group_predictable_variance_le {ι : Type*} [Fintype ι] {n r q : ℕ}
    (ratio : ℝ) (hratio : 1 < ratio) (u w : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio
      fun t => ((dyadicBin u amp t).card : ℝ)))
    (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (X : Fin n → Euclid q × Euclid r) (d : ℝ) (hd : 0 < d) :
    (∑ j ∈ range groups.length,
      (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2) *
        ‖operatorFrobenius (completedPrefixWitness w lo hi X
          (supportCut (dyadicGroupSupport u amp groups T) j))‖^2 / d) ≤
      (16*T*ratio^2/(3*(ratio-1)*d))*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  exact real_supported_group_predictable_variance_le ratio hratio u amp ha groups T hreg hflat hchain X
    (fun j => completedPrefixWitness w lo hi X (supportCut (dyadicGroupSupport u amp groups T) j))
    (fun j _ => norm_completedPrefixWitness_le_one w lo hi hlo hsep X _)
    (fun j _ => completedPrefixWitness_right_prefix w lo hi hlo X _) d hd

theorem real_actual_group_predictable_variance_mass_le {ι : Type*} [Fintype ι] {n r q : ℕ}
    (ratio : ℝ) (hratio : 1 < ratio) (u w : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio
      fun t => ((dyadicBin u amp t).card : ℝ)))
    (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (X : Fin n → Euclid q × Euclid r) (d : ℝ) (hd : 0 < d) :
    (∑ j ∈ range groups.length,
      (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2) *
        ‖operatorFrobenius (completedPrefixWitness w lo hi X
          (supportCut (dyadicGroupSupport u amp groups T) j))‖^2 / d) ≤
      (16*T*ratio^2/(3*(ratio-1)*d))*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  exact real_actual_group_predictable_variance_le ratio hratio u w amp ha groups T hreg hflat hchain
    lo hi hlo hsep X d hd

/-- The exact source partial-polar witnesses satisfy the arbitrary-real-q
random variance display, with no logarithmic loss and no supplied energy bound. -/
theorem paper_exact_group_predictable_variance_le {ι : Type*} [Fintype ι] {n r q : ℕ}
    (ratio : ℝ) (hratio : 1 < ratio) (u w : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio
      fun t => ((dyadicBin u amp t).card : ℝ)))
    (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (X : Fin n → Euclid q × Euclid r) (d : ℝ) (hd : 0 < d) :
    (∑ j ∈ range groups.length,
      (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2) *
        ‖operatorFrobenius (GaussianEllipsoid.PaperCanonicalPolar.exactCompletedPrefix w lo hi X
          (supportCut (dyadicGroupSupport u amp groups T) j))‖^2 / d) ≤
      (16*T*ratio^2/(3*(ratio-1)*d))*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  apply real_supported_group_predictable_variance_le ratio hratio u amp ha groups T hreg hflat hchain X
    (fun j => GaussianEllipsoid.PaperCanonicalPolar.exactCompletedPrefix w lo hi X
      (supportCut (dyadicGroupSupport u amp groups T) j))
  · intro j _
    exact (GaussianEllipsoid.PaperCanonicalPolar.exactCompletedPrefix_norm_energy w lo hi hlo hsep X _).1
  · intro j _
    exact (GaussianEllipsoid.PaperCanonicalPolar.exactCompletedPrefix_norm_energy w lo hi hlo hsep X _).2.1
  · exact hd
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.real_actual_group_predictable_variance_le

#print axioms GaussianEllipsoidCandidate.real_supported_group_predictable_variance_le

#print axioms GaussianEllipsoidCandidate.real_actual_group_predictable_variance_mass_le

#print axioms GaussianEllipsoidCandidate.paper_exact_group_predictable_variance_le
