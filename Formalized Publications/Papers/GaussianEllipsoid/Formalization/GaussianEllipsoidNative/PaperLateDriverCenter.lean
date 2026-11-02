import PaperTranslatedBlocks

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianBilinearTransport GaussianEllipsoid GaussianEllipsoid.SmallBall
open scoped ENNReal BigOperators
namespace GaussianPairedBlocks

/-- Uniform deterministic-center late-driver bound, before conditioning on outside samples. -/
theorem late_driver_center_smallball_ambient {n d h : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ)
    (C : FrobeniusMatrix h h)
    (hm : 64 ≤ min S.card d) (hdh : d ≤ 3*h) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlower : ∀ i ∈ S, ℓ ≤ |w i|) (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    tensorGaussianLaw n h
      {z | spectralNuclearNorm (flatBilinear (d:ℝ) h n (driverCoefficients S w) z-C) ≤
        (1/1048576:ℝ) * Real.sqrt d * (∑ i ∈ S, |w i|) *
          Real.sqrt ((min S.card d:ℕ)/(S.card:ℝ))} ≤
      ENNReal.ofReal (Real.exp (-(d:ℝ)*(min S.card d:ℕ)/1024)) := by
  let v := driverCoefficients S w
  let σ := Real.sqrt (∑ i, (v i)^2)
  have henergy : 0 < ∑ i, (v i)^2 := by
    have hs : (0:ℝ) < S.card := by exact_mod_cast (show 0<S.card by omega)
    exact lt_of_lt_of_le (mul_pos hs (sq_pos_of_pos hℓ))
      (driver_energy_lower S w hℓ.le hlower)
  have hσ : 0 < σ := Real.sqrt_pos.mpr henergy
  have hσsq : ∑ i, (v i)^2 = σ^2 := (Real.sq_sqrt henergy.le).symm
  have hcap : ∀ i, (v i)^2 ≤ σ^2*(2*(lateBlockDim S.card d:ℝ))⁻¹ := by
    rw [← hσsq]
    exact driver_cap S w hm hℓ hlower hupper
  obtain ⟨hh,hr,hu,hl,hJ⟩ := lateBlock_geometry_ambient hm hdh
  have hd : 0 < d := by omega
  have hp := paired_center_smallball
    (consecutiveBlocks h (lateBlockDim S.card d))
    (consecutiveBlocks h (lateBlockDim S.card d))
    hh hr (show lateBlockDim S.card d = 2*(min S.card d/32) from rfl)
    v hσ (Nat.cast_pos.mpr hd) hσsq hcap C
  have hM : 0 ≤ ∑ i ∈ S, |w i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmass : (∑ i ∈ S, |w i|)^2 ≤ (S.card:ℝ)*σ^2 := by
    rw [← hσsq]
    exact driver_mass_sq_le S w
  have hthreshold := lateBlock_threshold_ambient hm hdh hM hσ hmass
  have hsub : {z | spectralNuclearNorm (flatBilinear (d:ℝ) h n v z-C) ≤
      (1/1048576:ℝ)*Real.sqrt d*(∑ i ∈ S, |w i|)*Real.sqrt ((min S.card d:ℕ)/(S.card:ℝ))} ⊆
      {z | spectralNuclearNorm (flatBilinear (d:ℝ) h n v z-C) ≤
      ((h / lateBlockDim S.card d:ℕ):ℝ)/2 * blockThreshold σ d (lateBlockDim S.card d)} :=
    fun _ hz => hz.trans hthreshold
  exact ((measure_mono hsub).trans hp).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
    have := lateBlock_exponent_ambient hm hdh
    linarith)))


/-- Literal strict-event form with a common numerical constant in the radius and exponent.
No positivity of the amplitude parameter is added: the zero-amplitude endpoint is empty. -/
theorem late_driver_arbitrary_center {n d h : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ)
    (C : FrobeniusMatrix h h) (hm : 64 ≤ min S.card d) (hdh : d ≤ 3*h)
    {ℓ : ℝ} (hlower : ∀ i ∈ S, ℓ ≤ |w i|) (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    tensorGaussianLaw n h
      {z | spectralNuclearNorm (C+flatBilinear (d:ℝ) h n (driverCoefficients S w) z) <
        (1/1048576:ℝ)*Real.sqrt d*(∑ i ∈ S, |w i|)*
          Real.sqrt ((min S.card d:ℕ)/(S.card:ℝ))} ≤
      ENNReal.ofReal (Real.exp (-(1/1048576:ℝ)*(d:ℝ)*(min S.card d:ℕ))) := by
  by_cases hℓ : 0 < ℓ
  · have hp := late_driver_center_smallball_ambient S w (-C) hm hdh hℓ hlower hupper
    apply (measure_mono ?_).trans (hp.trans ?_)
    · intro z hz
      have hz' : spectralNuclearNorm (C+flatBilinear (d:ℝ) h n (driverCoefficients S w) z) <
          (1/1048576:ℝ)*Real.sqrt d*(∑ i ∈ S, |w i|)*
            Real.sqrt ((min S.card d:ℕ)/(S.card:ℝ)) := hz
      change spectralNuclearNorm (flatBilinear (d:ℝ) h n (driverCoefficients S w) z-(-C)) ≤ _
      simpa only [sub_neg_eq_add,add_comm] using hz'.le
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (show (0:ℝ) ≤ d by positivity)
        (show (0:ℝ) ≤ (min S.card d:ℕ) by positivity)]
  · have hmass : ∑ i ∈ S, |w i| = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact le_antisymm (by linarith [hupper i hi]) (abs_nonneg _)
    simp only [hmass,mul_zero,zero_mul]
    have hempty : {z | spectralNuclearNorm
        (C+flatBilinear (d:ℝ) h n (driverCoefficients S w) z) < 0} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      exact not_lt_of_ge (spectralNuclear_nonneg _)
    rw [hempty,measure_empty]
    exact zero_le

#print axioms late_driver_center_smallball_ambient
#print axioms late_driver_arbitrary_center
end GaussianPairedBlocks
