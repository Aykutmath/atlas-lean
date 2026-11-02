import BartlettDeterminantMoment
import CappedDeterminantExtended

noncomputable section
open MeasureTheory ProbabilityTheory Module Finset Matrix
open GaussianEllipsoid.CappedSimplex

namespace GaussianMixedNormHelpers

/-- Enumerating a uniform subset identifies its covariance with the ordinary
scaled row Gram matrix, with no probabilistic premise. -/
theorem weightedGram_uniform_subset_eq_scaled_gram
    {κ : Type*} [Fintype κ] [DecidableEq κ] {r m : ℕ}
    (g : κ → Fin r → ℝ) (T : Finset κ) (e : Fin m ≃ T) (a : ℝ) :
    weightedGram g (fun k => if k ∈ T then a else 0) =
      a • realGramMatrix (matrixEuclideanRows (fun p j => g (e j) p)) := by
  change weightedGram g (fun k => if k ∈ T then a else 0) =
    a • realGramMatrix (matrixEuclideanRows (Matrix.of (fun p j => g (e j) p)))
  rw [realGramMatrix_matrixEuclideanRows]
  ext p q
  simp only [weightedGram, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_mem]
  rw [← Finset.mul_sum]
  congr 1
  have h := Equiv.sum_comp e (fun k : T => g k p * g k q)
  rw [Finset.sum_coe_sort T (fun k => g k p * g k q)] at h
  simpa only [Finset.univ_inter] using h.symm

/-- Exact scalar determinant factor for an enumerated uniform subset. -/
theorem det_weightedGram_uniform_subset
    {κ : Type*} [Fintype κ] [DecidableEq κ] {r m : ℕ}
    (g : κ → Fin r → ℝ) (T : Finset κ) (e : Fin m ≃ T) (a : ℝ) :
    (weightedGram g (fun k => if k ∈ T then a else 0)).det =
      a ^ r * (realGramMatrix (matrixEuclideanRows (fun p j => g (e j) p))).det := by
  rw [weightedGram_uniform_subset_eq_scaled_gram g T e a, Matrix.det_smul, Fintype.card_fin]

/-- Paper-normalized determinant form used by the extended inverse-moment law. -/
theorem det_weightedGram_uniform_subset_inv
    {κ : Type*} [Fintype κ] [DecidableEq κ] {r m : ℕ}
    (g : κ → Fin r → ℝ) (T : Finset κ) (e : Fin m ≃ T) (a : ℝ) :
    (weightedGram g (fun k => if k ∈ T then a⁻¹ else 0)).det =
      (a ^ r)⁻¹ * (realGramMatrix (matrixEuclideanRows (fun p j => g (e j) p))).det := by
  rw [det_weightedGram_uniform_subset g T e a⁻¹, inv_pow]

end GaussianMixedNormHelpers

namespace GaussianMixedNormHelpers
/-- Deterministic/probability transport interface for the selected-column law.
The actual Gaussian instance is supplied separately, without treating this map
identity as a replacement assumption of the final moment theorem. -/
theorem selected_uniform_extended_moment_le_of_map
    {κ : Type*} [Fintype κ] [DecidableEq κ] (r s : ℕ) (hr : 0 < r)
    (μ : Measure (κ → Fin r → ℝ)) (T : Finset κ) (e : Fin (r + 2 * s) ≃ T)
    (hlaw : Measure.map
      (fun g : κ → Fin r → ℝ => matrixEuclideanRows (fun p j => g (e j) p)) μ =
        Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin (r + 2 * s)))) :
    extendedMoment μ s (fun k => if k ∈ T then (2 * (r : ℝ))⁻¹ else 0) ≤
      ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s)) := by
  have hm : Measurable
      (fun g : κ → Fin r → ℝ => matrixEuclideanRows (fun p j => g (e j) p)) := by
    apply measurable_pi_iff.mpr
    intro p
    change Measurable (fun g : κ → Fin r → ℝ =>
      (MeasurableEquiv.toLp 2 ((Fin (r + 2 * s)) → ℝ)) (fun j => g (e j) p))
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).measurable.comp
    exact measurable_pi_iff.mpr (fun j =>
      (measurable_pi_apply p).comp (measurable_pi_apply (e j : κ)))
  have hi := lintegral_map (μ := μ)
    (f := fun f : Fin r → EuclideanSpace ℝ (Fin (r + 2 * s)) =>
      ((ENNReal.ofReal (((2 * (r : ℝ)) ^ r)⁻¹ * (realGramMatrix f).det)) ^ s)⁻¹)
    (by
      have hmGram : Measurable (fun f : Fin r → EuclideanSpace ℝ (Fin (r + 2 * s)) =>
          (realGramMatrix f).det) := by
        apply Continuous.measurable
        apply Continuous.matrix_det
        unfold realGramMatrix
        fun_prop
      exact ((hmGram.const_mul _).ennreal_ofReal.pow_const s).inv) hm
  rw [hlaw] at hi
  unfold extendedMoment extendedDetInv
  have heq : (fun g : κ → Fin r → ℝ =>
      ((ENNReal.ofReal (weightedGram g (fun k => if k ∈ T then (2 * (r : ℝ))⁻¹ else 0)).det)^s)⁻¹) =
      (fun g => ((ENNReal.ofReal (((2 * (r : ℝ)) ^ r)⁻¹ *
        (realGramMatrix (matrixEuclideanRows (fun p j => g (e j) p))).det)) ^ s)⁻¹) := by
    funext g
    rw [det_weightedGram_uniform_subset_inv g T e]
  rw [heq, ← hi]
  exact gaussianRows_scaled_extended_inverse_det_moment_le r s hr

end GaussianMixedNormHelpers

namespace GaussianMixedNormHelpers
/-- A reciprocal cap and unit total mass force at least `m` available columns. -/
theorem exists_card_subset_of_reciprocal_cap
    {κ : Type*} [Fintype κ] [DecidableEq κ] {m : ℕ} (hm : 0 < m)
    {w : κ → ℝ} (hw : w ∈ slice ((m : ℝ)⁻¹) 1) :
    ∃ T : Finset κ, T.card = m := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hsum : (1 : ℝ) ≤ (Fintype.card κ : ℝ) * (m : ℝ)⁻¹ := by
    calc
      1 = ∑ k, w k := hw.2.symm
      _ ≤ ∑ _ : κ, (m : ℝ)⁻¹ := Finset.sum_le_sum (fun k _ => (hw.1 k).2)
      _ = _ := by simp
  have hcardR : (m : ℝ) ≤ Fintype.card κ := by
    have h := (le_div_iff₀ hmR).mp (show (1 : ℝ) ≤ (Fintype.card κ : ℝ) / m by
      simpa only [div_eq_mul_inv] using hsum)
    simpa only [one_mul] using h
  have hcard : m ≤ (Finset.univ : Finset κ).card := by
    simpa only [Finset.card_univ] using (show m ≤ Fintype.card κ by exact_mod_cast hcardR)
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨T, hT⟩
end GaussianMixedNormHelpers
