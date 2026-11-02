import PaperLateDriverConditional

noncomputable section
open MeasureTheory ProbabilityTheory Finset GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid GaussianEllipsoid.SmallBall GaussianEllipsoid.ProjectedClusters GaussianBilinearTransport
open scoped ENNReal BigOperators
namespace GaussianPairedBlocks

/-- Explicit conversion of macroscopic support to the large-minimum regime. -/
theorem macroscopic_support_eventually_large {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ d₀ : ℕ, ∀ {s d : ℕ}, d₀ ≤ d → c₀*(d:ℝ) ≤ s → 64 ≤ min s d := by
  let a := min c₀ 1
  have ha : 0 < a := lt_min hc₀ zero_lt_one
  obtain ⟨d₀,hd₀⟩ := exists_nat_ge (64/a)
  refine ⟨d₀,?_⟩
  intro s d hlarge hsize
  have hdim : 64/a ≤ (d:ℝ) := hd₀.trans (Nat.cast_le.mpr hlarge)
  have hprod : 64 ≤ a*(d:ℝ) := by
    have hh := (div_le_iff₀ ha).mp hdim
    nlinarith
  have hs : (64:ℝ) ≤ s := hprod.trans
    ((mul_le_mul_of_nonneg_right (min_le_left c₀ 1) (Nat.cast_nonneg d)).trans hsize)
  have hd : (64:ℝ) ≤ d := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right c₀ 1) (Nat.cast_nonneg d)
    dsimp [a] at hprod
    nlinarith
  exact le_min (by exact_mod_cast hs) (by exact_mod_cast hd)

/-- Paper macroscopic late-driver quantifiers: the numerical constant is universal,
and the starting dimension is chosen before the sample size, support, coefficients,
and arbitrary outside-measurable center. The upper size bound is permitted verbatim
although the stronger proved estimate does not need it. -/
theorem paper_late_driver_comparison (c₀ K : ℝ) (hc₀ : 0 < c₀) (_hK : 0 < K) :
    ∃ d₀ : ℕ, ∀ {N s d : ℕ}, d₀ ≤ d → c₀*(d:ℝ) ≤ s → (s:ℝ) ≤ K*d →
      ∀ (eS : Fin s ↪ Fin N)
        (w : (GaussianEntries N (d/2) × GaussianEntries N (d/2)) → Fin s → ℝ)
        (C : (GaussianEntries N (d/2) × GaussianEntries N (d/2)) → FrobeniusMatrix (d/2) (d/2)),
        Measurable[outsideSampleSigmaField eS] w → Measurable[outsideSampleSigmaField eS] C →
        (∀ᵐ ω ∂tensorGaussianLaw N (d/2), ∃ ℓ : ℝ,
          (∀ i, ℓ ≤ |w ω i|) ∧ ∀ i, |w ω i| ≤ 2*ℓ) →
        (tensorGaussianLaw N (d/2))[({ω | spectralNuclearNorm
          (C ω+flatBilinear (d:ℝ) (d/2) s (w ω) (selectSample eS ω)) <
          (1/1048576:ℝ)*Real.sqrt d*(∑ i, |w ω i|)*Real.sqrt ((min s d:ℕ)/(s:ℝ))}).indicator
          (1 : (GaussianEntries N (d/2) × GaussianEntries N (d/2)) → ℝ) |
            outsideSampleSigmaField eS] ≤ᵐ[tensorGaussianLaw N (d/2)]
          fun _ => Real.exp (-(1/1048576:ℝ)*(d:ℝ)*(min s d:ℕ)) := by
  obtain ⟨d₀,hd₀⟩ := macroscopic_support_eventually_large hc₀
  refine ⟨d₀,?_⟩
  intro N s d hlarge hlow _hup eS w C hw hC hamp
  exact late_driver_outside_half_dimension_conditional eS (hd₀ hlarge hlow) w C hw hC hamp

#print axioms paper_late_driver_comparison
end GaussianPairedBlocks
