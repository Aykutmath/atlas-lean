import GaussianLateDriver

/-! Reconstructed source, 2026-10-03. This is new text, not recovered original bytes. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianBilinearTransport GaussianEllipsoid GaussianEllipsoid.SmallBall GaussianEllipsoidCandidate
open scoped ENNReal BigOperators
namespace GaussianPairedBlocks

/-- A deterministic center survives normalization; no symmetry of the center is required. -/
theorem flatBilinear_center_smallball {r n s : ℕ} (hr : 0 < r) (hrs : r=2*s)
    (v : Fin n → ℝ) {σ d : ℝ} (hσ : 0<σ) (hd : 0<d)
    (hvsum : ∑ i,(v i)^2=σ^2) (hvcap : ∀ i,(v i)^2 ≤ σ^2*(2*(r:ℝ))⁻¹)
    (C : FrobeniusMatrix r r) :
    (tensorGaussianLaw n r).real {z | spectralNuclearNorm (flatBilinear d r n v z-C) ≤
      blockThreshold σ d r} ≤ Real.exp (-(r*r:ℕ)) := by
  let vn : Fin n → ℝ := σ⁻¹ • v
  let a := σ*Real.sqrt (r:ℝ)/Real.sqrt d
  have hrR : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ha : 0<a := by dsimp [a]; positivity
  have hsum : ∑ i,(vn i)^2=1 := by
    simp only [vn, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hvsum]
    field_simp
  have hcap : ∀ i,(vn i)^2 ≤ (2*(r:ℝ))⁻¹ := by
    intro i
    calc
      (vn i)^2 = (σ⁻¹)^2*(v i)^2 := by simp [vn,mul_pow]
      _ ≤ (σ⁻¹)^2*(σ^2*(2*(r:ℝ))⁻¹) := mul_le_mul_of_nonneg_left (hvcap i) (sq_nonneg _)
      _ = _ := by field_simp
  have hp := gaussian_bilinear_disjoint_nuclear_unit_tail r n s hr hrs 0 vn
    (by simp) hsum hcap (a⁻¹ • C) (by norm_num : (0:ℝ)<1/1024)
  simp only [zero_add] at hp
  have hy (p : BilinearSample r n) :
      bilinearScaled d r n v p-C = a • (bilinearFrobenius r n vn p-a⁻¹ • C) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    congr 1
    rw [bilinearFrobenius_smul, smul_smul]
    unfold bilinearScaled
    congr 1
    dsimp [a]
    field_simp <;> ring
  have ht : blockThreshold σ d r = a*((1/1024:ℝ)*r) := by
    unfold blockThreshold
    dsimp [a]
    ring
  have heq : {p | spectralNuclearNorm (bilinearScaled d r n v p-C) ≤ blockThreshold σ d r} =
      {p | spectralNuclearNorm (bilinearFrobenius r n vn p-a⁻¹ • C) ≤ (1/1024:ℝ)*r} := by
    ext p
    simp only [Set.mem_setOf_eq]
    rw [hy, spectralNuclear_smul, abs_of_pos ha, ht, mul_le_mul_iff_right₀ ha]
  have hmeas : MeasurableSet {p | spectralNuclearNorm (bilinearScaled d r n v p-C) ≤
      blockThreshold σ d r} := measurableSet_le
    ((continuous_spectralNuclear r r).measurable.comp
      ((measurable_bilinearScaled d r n v).sub measurable_const)) measurable_const
  have hprob : (tensorGaussianLaw n r).real {z | spectralNuclearNorm (flatBilinear d r n v z-C) ≤
      blockThreshold σ d r} = (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearScaled d r n v p-C) ≤ blockThreshold σ d r} := by
    unfold Measure.real
    rw [← (flatToSmallBall_preserving n r).map_eq,
      Measure.map_apply (flatToSmallBall_measurable n r) hmeas]
    rfl
  rw [hprob, heq]
  apply hp.trans
  have he : Real.exp (1:ℝ)<3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hb : 160*(1/1024:ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
    nlinarith
  have hb' := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 160*(1/1024:ℝ)) hb (r*r)
  rw [← Real.exp_nat_mul] at hb'
  convert hb' using 1 <;> congr 1 <;> ring

/-- The same deterministic center is compressed into each independent paired
block before majority amplification. -/
theorem paired_center_smallball {n h J r s : ℕ}
    (eL eR : Fin J × Fin r ↪ Fin h) (hh : 0<h) (hr : 0<r) (hrs : r=2*s)
    (v : Fin n → ℝ) {σ d : ℝ} (hσ : 0<σ) (hd : 0<d)
    (hvsum : ∑ i,(v i)^2=σ^2) (hvcap : ∀ i,(v i)^2 ≤ σ^2*(2*(r:ℝ))⁻¹)
    (C : FrobeniusMatrix h h) :
    tensorGaussianLaw n h {z | spectralNuclearNorm (flatBilinear d h n v z-C) ≤
      (J:ℝ)/2*blockThreshold σ d r} ≤
      ENNReal.ofReal (Real.exp (-(J:ℝ)*(r:ℝ)^2/4)) := by
  let E : Fin J → Set (GaussianEntries n r × GaussianEntries n r) := fun j =>
    {z | spectralNuclearNorm (flatBilinear d r n v z-coordinateBlock eL eR C j) ≤
      blockThreshold σ d r}
  have hE : ∀ j, MeasurableSet (E j) := fun j => measurableSet_le
    ((continuous_spectralNuclear r r).measurable.comp
      ((measurable_flatBilinear d r n v).sub measurable_const)) measurable_const
  have hp : ∀ j, tensorGaussianLaw n r (E j) ≤ ENNReal.ofReal (Real.exp (-(r*r:ℕ))) :=
    fun j => measure_le_of_real_le _ _ (flatBilinear_center_smallball hr hrs v hσ hd hvsum hvcap
      (coordinateBlock eL eR C j))
  have hT : 0<blockThreshold σ d r := by
    have : (0:ℝ)<r := Nat.cast_pos.mpr hr
    unfold blockThreshold
    positivity
  have hsub : {z | spectralNuclearNorm (flatBilinear d h n v z-C) ≤
      (J:ℝ)/2*blockThreshold σ d r} ⊆
      {z | (J+1)/2 ≤ badCount (fun j => pairedBlock eL eR j ⁻¹' E j) z} := by
    intro z hz
    have hpinch := sum_spectralNuclear_coordinateBlock_le eL eR (flatBilinear d h n v z-C)
    have he (j : Fin J) : coordinateBlock eL eR (flatBilinear d h n v z-C) j =
        flatBilinear d r n v (pairedBlock eL eR j z)-coordinateBlock eL eR C j := by
      have hs : coordinateBlock eL eR (flatBilinear d h n v z-C) j =
          coordinateBlock eL eR (flatBilinear d h n v z) j-coordinateBlock eL eR C j := by
        ext b a
        rfl
      rw [hs,coordinateBlock_flatBilinear eL eR hh hr]
    simp_rw [he] at hpinch
    exact half_bad_of_sum_le _ (fun _ => spectralNuclear_nonneg _) hT (hpinch.trans hz)
  exact ((measure_mono hsub).trans (measure_many_paired_bad eL eR E hE _ hp ((J+1)/2))).trans
    (exponential_majority_bound J r (by omega))

end GaussianPairedBlocks

#print axioms GaussianPairedBlocks.paired_center_smallball
