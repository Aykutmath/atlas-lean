import RealWishartExtended
import RealDeterminantExtended
import GaussianSelectedColumns
import SelectedCovariance

noncomputable section
open MeasureTheory ProbabilityTheory Module Finset Matrix
open GaussianEllipsoid.CappedSimplex GaussianTensorMoments
namespace GaussianMixedNormHelpers

theorem selected_uniform_extended_real_moment
    {κ : Type*} [Fintype κ] [DecidableEq κ] (r k : ℕ) (hkr : r ≤ k)
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (hshape : ∀ j : Fin r, s < ((k-j.val:ℕ):ℝ)/2)
    (T : Finset κ) (e : Fin k ≃ T) :
    extendedRealMoment (Measure.pi (fun _ : κ => gaussianProductLaw (Fin r))) s
      (fun i => if i ∈ T then a else 0) =
    ENNReal.ofReal ((a^r)^(-s) *
      ∏ j : Fin r, (2:ℝ)^(-s) *
        (Real.Gamma (((k-j.val:ℕ):ℝ)/2-s) / Real.Gamma (((k-j.val:ℕ):ℝ)/2))) := by
  let μ := Measure.pi (fun _ : κ => gaussianProductLaw (Fin r))
  let U := fun g : κ → Fin r → ℝ => matrixEuclideanRows (fun p j => g (e j) p)
  have hU : Measurable U := by
    apply measurable_pi_iff.mpr
    intro p
    change Measurable (fun g : κ → Fin r → ℝ =>
      (MeasurableEquiv.toLp 2 ((Fin k) → ℝ)) (fun j => g (e j) p))
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).measurable.comp
    exact measurable_pi_iff.mpr (fun j =>
      (measurable_pi_apply p).comp (measurable_pi_apply (e j : κ)))
  have hmap := gaussianColumns_map_selectedRows r k (fun j => (e j:κ))
    (Subtype.val_injective.comp e.injective)
  have hmGram : Measurable (fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
      (realGramMatrix f).det) := by
    apply Continuous.measurable
    apply Continuous.matrix_det
    unfold realGramMatrix
    fun_prop
  have hi := lintegral_map (μ := μ)
    (f := fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
      (ENNReal.ofReal (realGramMatrix f).det)^(-s))
    (hmGram.ennreal_ofReal.pow_const (-s)) hU
  rw [hmap] at hi
  have heq : (fun g : κ → Fin r → ℝ => extendedRealDetInv s
      (weightedGram g (fun i => if i ∈ T then a else 0))) =
      (fun g => ENNReal.ofReal ((a^r)^(-s)) *
        (ENNReal.ofReal (realGramMatrix (U g)).det)^(-s)) := by
    funext g
    unfold extendedRealDetInv
    rw [← ENNReal.rpow_neg, det_weightedGram_uniform_subset g T e,
      ENNReal.ofReal_mul (pow_nonneg ha.le _),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.ofReal_rpow_of_pos (pow_pos ha _)]
  unfold extendedRealMoment
  rw [heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hi,
    gaussianRows_extended_negative_real_det_moment r k hkr s hs hshape,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (pow_nonneg ha.le _) _)]
end GaussianMixedNormHelpers
#print axioms GaussianMixedNormHelpers.selected_uniform_extended_real_moment
