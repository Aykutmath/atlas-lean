import GaussianBilinearSmallBall
import DeterminantMonotonicity
import PolarDuality

noncomputable section
open MeasureTheory Finset
open GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid.CappedSimplex
open scoped ENNReal

namespace GaussianEllipsoid.SmallBall

/-- Scalar linearity of the actual vectorized bilinear map. -/
theorem bilinearFlat_smul (r n : ℕ) (c : ℝ) (z : Fin n → ℝ) (p : BilinearSample r n) :
    bilinearFlat r n (c • z) p = c • bilinearFlat r n z p := by
  ext pq
  rcases pq with ⟨a, b⟩
  change matrixCLM (bilinearDriver (Real.sqrt (r : ℝ))⁻¹ (c • z) p.1) p.2 (a, b) =
    c * matrixCLM (bilinearDriver (Real.sqrt (r : ℝ))⁻¹ z p.1) p.2 (a, b)
  rw [matrixCLM_bilinearDriver_apply, matrixCLM_bilinearDriver_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc c]
  rw [← Finset.mul_sum]
  ring

theorem bilinearFrobenius_smul (r n : ℕ) (c : ℝ) (z : Fin n → ℝ) (p : BilinearSample r n) :
    bilinearFrobenius r n (c • z) p = c • bilinearFrobenius r n z p := by
  simp only [bilinearFrobenius, bilinearFlat_smul, map_smul]

/-- An arbitrary disjoint head needs no conditioning or separate law transport:
its positive covariance only improves the tail's determinant moment. -/
theorem gaussian_bilinear_disjoint_nuclear_unit_tail (r n s : ℕ)
    (hr : 0 < r) (hrs : r = 2 * s) (u v : Fin n → ℝ)
    (hdisj : ∀ i, u i * v i = 0)
    (hvsum : ∑ i, (v i) ^ 2 = 1)
    (hvcap : ∀ i, (v i) ^ 2 ≤ (2 * (r : ℝ))⁻¹)
    (M : FrobeniusMatrix r r) {ν : ℝ} (hν : 0 < ν) :
    (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearFrobenius r n (u + v) p - M) ≤ ν * r} ≤
      (160 * ν) ^ (r * r) := by
  let μ := Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin r))
  have hMoment : extendedMoment μ s (fun i => ((u + v) i) ^ 2) ≤
      ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s)) := by
    exact (extendedMoment_disjoint_le μ s u v hdisj).trans
      (gaussian_capped_even_extended_moment r s hr hrs
        ⟨(fun i => ⟨sq_nonneg _, hvcap i⟩), hvsum⟩)
  apply nuclear_smallball_polynomial (bilinearGaussianSampleLaw r n) r hr
    (bilinearFrobenius r n (u + v)) _ M hν
  intro C t ht
  have h := bilinear_frobenius_smallball_of_moment r n s hr hrs (u + v) hMoment
    (frobeniusEquivEuclidean r r C) ht
  have hn : ∀ p, ‖bilinearFrobenius r n (u + v) p - C‖ =
      ‖bilinearFlat r n (u + v) p - frobeniusEquivEuclidean r r C‖ := by
    intro p
    rw [← (frobeniusEquivEuclidean r r).norm_map (bilinearFrobenius r n (u + v) p - C), map_sub]
    simp only [bilinearFrobenius, LinearIsometryEquiv.apply_symm_apply]
  have heq : {p | ‖bilinearFrobenius r n (u + v) p - C‖ ≤ t * Real.sqrt (r : ℝ)} =
      {p | ‖bilinearFlat r n (u + v) p - frobeniusEquivEuclidean r r C‖ ≤ t * Real.sqrt (r : ℝ)} := by
    ext p
    simp only [Set.mem_setOf_eq]
    rw [hn]
  rw [heq]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

/-- The original d^(-1/2) bilinear scaling, in the same actual Gaussian sample space. -/
def bilinearScaled (d : ℝ) (r n : ℕ) (z : Fin n → ℝ) (p : BilinearSample r n) :
    FrobeniusMatrix r r :=
  (Real.sqrt (r : ℝ) / Real.sqrt d) • bilinearFrobenius r n z p

theorem bilinearScaled_entry {d : ℝ} (r n : ℕ) (hr : 0 < r)
    (z : Fin n → ℝ) (p : BilinearSample r n) (a b : Fin r) :
    frobeniusToMatrix (bilinearScaled d r n z p) a b =
      (Real.sqrt d)⁻¹ * ∑ i, z i * p.1 i a * p.2 (i, b) := by
  change (Real.sqrt (r : ℝ) / Real.sqrt d) *
    frobeniusToMatrix (bilinearFrobenius r n z p) a b = _
  rw [bilinearFrobenius_entry]
  have hs : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr))
  by_cases hD : Real.sqrt d = 0
  · simp [hD]
  · field_simp [hs, hD] <;> ring

/-- Actual global-law disjoint-head/tail small ball, in the paper's scaling.
No head-size, head-sign, head-magnitude, or independent-center assumption is needed.
The hypotheses concern only disjointness and the nonzero capped tail. -/
theorem gaussian_bilinear_disjoint_scaled_nuclear_smallball (r n s : ℕ)
    (hr : 0 < r) (hrs : r = 2 * s) (u v : Fin n → ℝ)
    (hdisj : ∀ i, u i * v i = 0) {σ d T : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (hT : 0 < T)
    (hvsum : ∑ i, (v i) ^ 2 = σ ^ 2)
    (hvcap : ∀ i, (v i) ^ 2 ≤ σ ^ 2 * (2 * (r : ℝ))⁻¹) :
    (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearScaled d r n (u + v) p) ≤ T} ≤
      (160 * T * Real.sqrt d / (σ * (r : ℝ) * Real.sqrt (r : ℝ))) ^ (r * r) := by
  let un : Fin n → ℝ := σ⁻¹ • u
  let vn : Fin n → ℝ := σ⁻¹ • v
  have hsum : ∑ i, (vn i) ^ 2 = 1 := by
    simp only [vn, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hvsum]
    field_simp
  have hcap : ∀ i, (vn i) ^ 2 ≤ (2 * (r : ℝ))⁻¹ := by
    intro i
    calc (vn i) ^ 2 = (σ⁻¹) ^ 2 * (v i) ^ 2 := by simp only [vn, Pi.smul_apply, smul_eq_mul, mul_pow]
      _ ≤ (σ⁻¹) ^ 2 * (σ ^ 2 * (2 * (r : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left (hvcap i) (sq_nonneg _)
      _ = _ := by field_simp
  have hdisj' : ∀ i, un i * vn i = 0 := by
    intro i
    change (σ⁻¹ * u i) * (σ⁻¹ * v i) = 0
    calc _ = σ⁻¹ * σ⁻¹ * (u i * v i) := by ring
      _ = 0 := by rw [hdisj i]; ring
  have hc : un + vn = σ⁻¹ • (u + v) := by
    ext i
    simp only [un, vn, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  let a : ℝ := σ * Real.sqrt (r : ℝ) / Real.sqrt d
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have ha : 0 < a := by dsimp [a]; positivity
  let ν : ℝ := T / (a * (r : ℝ))
  have hν : 0 < ν := div_pos hT (mul_pos ha hrR)
  have h := gaussian_bilinear_disjoint_nuclear_unit_tail r n s hr hrs un vn hdisj' hsum hcap 0 hν
  simp only [sub_zero] at h
  have hy : ∀ p, bilinearScaled d r n (u + v) p = a • bilinearFrobenius r n (un + vn) p := by
    intro p
    rw [hc, bilinearFrobenius_smul, smul_smul]
    unfold bilinearScaled
    congr 1
    dsimp [a]
    field_simp <;> ring
  have hνr : ν * (r : ℝ) = T / a := by
    dsimp [ν]
    field_simp <;> ring
  have heq : {p | spectralNuclearNorm (bilinearScaled d r n (u + v) p) ≤ T} =
      {p | spectralNuclearNorm (bilinearFrobenius r n (un + vn) p) ≤ ν * r} := by
    ext p
    simp only [Set.mem_setOf_eq]
    rw [hy, spectralNuclear_smul, abs_of_pos ha, hνr, le_div_iff₀ ha]
    rw [mul_comm a]
  rw [heq]
  have hbase : 160 * ν = 160 * T * Real.sqrt d / (σ * (r : ℝ) * Real.sqrt (r : ℝ)) := by
    dsimp [ν, a]
    field_simp <;> ring
  simpa only [hbase] using h

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.gaussian_bilinear_disjoint_nuclear_unit_tail
#print axioms GaussianEllipsoid.SmallBall.gaussian_bilinear_disjoint_scaled_nuclear_smallball
