import SupportPermutationSynthesis
import ActualGroupMass

noncomputable section
open Finset MeasureTheory GaussianEllipsoid
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Canonical deterministic row permutation for the paper's actual retained
dyadic groups, in their existing record order. -/
def actualDyadicSupportPermutation {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) : Equiv.Perm (Fin n) :=
  supportOrderPermutation (dyadicGroupSupport u amp groups T)
    (actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl)

/-- Actual dyadic groups become exact consecutive row blocks. -/
theorem actualDyadicSupportPermutation_group {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (j : ℕ) (hj : j < groups.length) (i : Fin n) :
    i ∈ dyadicGroupSupport u amp groups T j ↔
      supportCut (dyadicGroupSupport u amp groups T) j ≤
        (actualDyadicSupportPermutation u amp ha groups T hreg hflat i).val ∧
      (actualDyadicSupportPermutation u amp ha groups T hreg hflat i).val <
        supportCut (dyadicGroupSupport u amp groups T) (j+1) :=
  supportOrderPermutation_mem_iff _ _ j hj i

/-- The exact numerical cut is the sum of the actual dyadic group sizes. -/
theorem actual_dyadic_supportCut_cast {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T k : ℕ) :
    (supportCut (dyadicGroupSupport u amp groups T) k : ℝ) =
      ∑ j ∈ range k, dyadicGroupSize u amp groups T j := by
  simp only [supportCut,Nat.cast_sum,dyadicGroupSize]

/-- The retained vector becomes precisely the initial-support cutoff of the
same permuted original vector; all appended unused rows have zero coefficient. -/
theorem actualDyadicSupportPermutation_retained {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) :
    permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat)
      (retainedGroupVector u amp groups T) =
    fun i => if i.val < supportCut (dyadicGroupSupport u amp groups T) groups.length
      then permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat) u i
      else 0 := by
  classical
  have heq : retainedGroupVector u amp groups T =
      fun i => if i ∈ (range groups.length).biUnion (dyadicGroupSupport u amp groups T)
        then u i else 0 := by
    funext i
    simp only [retainedGroupVector,retainedGroupUnion_eq_indexed,indexedGroupUnion,mem_biUnion]
  rw [heq]
  exact permuteRows_prefix_restriction _ _ groups.length le_rfl u

/-- Direct original Gaussian samples may first be split into the canonical
(b,a) rows and then moved to the actual dyadic order, with the same exact law. -/
theorem actualDyadicSupportPermutation_extractedRows_preserving {n d h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (eL eR : Fin h ↪ Fin d)
    (hdis : ∀ a b, eL a ≠ eR b) :
    MeasurePreserving
      (fun X => permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat)
        (extractedRows eL eR X))
      (Measure.pi (fun _ : Fin n => GaussianMixedNormHelpers.euclideanGaussianLaw (Fin d)))
      (gaussianBilinearSampleLaw (Fin n) h h) :=
  (permuteRows_preserving _ h h).comp (extractedRows_preserving eL eR hdis)

/-- Reordering the actual retained vector and rows preserves the actual synthesis exactly. -/
theorem actualDyadicSupportPermutation_synthesis {n q r : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid q × Euclid r) :
    bilinearSynthesis
      (permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat)
        (retainedGroupVector u amp groups T))
      (permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat) X) =
      bilinearSynthesis (retainedGroupVector u amp groups T) X :=
  bilinearSynthesis_permuteRows _ _ _

end GaussianEllipsoidCandidate
