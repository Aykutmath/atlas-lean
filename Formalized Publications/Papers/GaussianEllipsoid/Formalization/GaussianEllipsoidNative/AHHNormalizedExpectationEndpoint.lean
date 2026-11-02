import AHHNormalizedTensorMoment
import AHHActualGaussianWordBound
import AHHExpectationEdgeBridge
import AHHLiteralHaarJensen

/-! Unconditional upper expectation edge for the actual normalized Gaussian and
Haar product-state ensembles. The only asymptotic input is the sample aspect ratio. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology Matrix.Norms.L2Operator
namespace AHHGaussian

/-- Exact finite normalized-Gaussian norm bound, retaining the chosen moment
order, the full dimension factor, and both generating-function constants. -/
theorem actualGaussian_expected_norm_le_edgeFiniteBound (p : ℕ → ℕ)
    (h : ℕ) (hh : 1 ≤ h) :
    (∫ x, ‖AHHAlgebraBridges.cMatrixCLM
        (actualComplexCovariance (p h) h true true x)‖ ∂fourGaussianLaw (p h) h) ≤
      AHH.edgeFiniteBound p h := by
  have hm : 1 ≤ AHH.edgeMomentOrder h := AHH.edgeMomentOrder_pos h
  have hp := actualComplexCovariance_expectation_pow_le_wordSum (p h) h
    (AHH.edgeMomentOrder h) hh hm
  have hb := normalizedGaussian_word_moment_bound (p h) h (AHH.edgeMomentOrder h) hh
  have hpow := hp.trans hb
  have hr := AHH.scalar_root_bound
    (integral_nonneg (fun x => norm_nonneg _)) (sq_nonneg (h : ℝ))
    (le_trans zero_le_one (AHH.edgeR_ge_one (AHH.edgeA h) (AHH.edgeB p h)))
    (AHH.edgeL_pos (AHH.edgeA_pos h) (AHH.edgeB_nonneg p h)).le
    (AHH.edgeMomentOrder_pos h)
    (by simpa only [AHH.edgeA, AHH.edgeB, mul_assoc] using hpow)
  exact hr

/-- The zero-dimensional exception is identically zero, rather than an extra
hypothesis hidden in the asymptotic endpoint. -/
theorem actualGaussian_expected_norm_zero (n : ℕ) (s t : Bool) :
    (∫ x, ‖AHHAlgebraBridges.cMatrixCLM (actualComplexCovariance n 0 s t x)‖
      ∂fourGaussianLaw n 0) = 0 := by
  have hz (x : FourEntries n 0) :
      AHHAlgebraBridges.cMatrixCLM (actualComplexCovariance n 0 s t x) = 0 :=
    Subsingleton.elim _ _
  simp only [hz, norm_zero, integral_zero]

/-- Public normalized Gaussian upper edge. No recurrence, word law,
integrability hypothesis, or abstract moment sequence is assumed. -/
theorem normalizedGaussian_expectation_upper_edge (p : ℕ → ℕ) {x : ℝ}
    (hx : 0 < x)
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    (∀ h, 0 ≤ AHH.edgeError p x h) ∧
    AHH.edgeError p x =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    (∀ h : ℕ,
      (∫ z, ‖AHHAlgebraBridges.cMatrixCLM
          (actualComplexCovariance (p h) h true true z)‖ ∂fourGaussianLaw (p h) h) ≤
        (1 + Real.sqrt x) ^ 2 + AHH.edgeError p x h) := by
  have he := AHH.expectation_upper_edge_o1 p
    (fun h => ∫ z, ‖AHHAlgebraBridges.cMatrixCLM
      (actualComplexCovariance (p h) h true true z)‖ ∂fourGaussianLaw (p h) h)
    hx hp (actualGaussian_expected_norm_le_edgeFiniteBound p)
  refine ⟨he.1, he.2.1, ?_⟩
  intro h
  by_cases hh : 1 ≤ h
  · exact he.2.2 h hh
  · have hz : h = 0 := by omega
    subst h
    rw [actualGaussian_expected_norm_zero]
    exact add_nonneg (sq_nonneg _) (AHH.edgeError_nonneg p x 0)

/-- The sharp upper edge is uniform over all four literal sign choices. -/
theorem normalizedGaussian_all_signs_expectation_upper_edge (p : ℕ → ℕ) {x : ℝ}
    (hx : 0 < x)
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    (∀ h, 0 ≤ AHH.edgeError p x h) ∧
    AHH.edgeError p x =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    (∀ (h : ℕ) (s t : Bool),
      (∫ z, ‖AHHAlgebraBridges.cMatrixCLM
          (actualComplexCovariance (p h) h s t z)‖ ∂fourGaussianLaw (p h) h) ≤
        (1 + Real.sqrt x) ^ 2 + AHH.edgeError p x h) := by
  have he := normalizedGaussian_expectation_upper_edge p hx hp
  refine ⟨he.1, he.2.1, ?_⟩
  intro h s t
  by_cases hh : 0 < h
  · rw [AHHRadial.actualComplexCovariance_expected_norm_sign_invariant (p h) h hh s t]
    exact he.2.2 h
  · have hz : h = 0 := by omega
    subst h
    rw [actualGaussian_expected_norm_zero]
    exact add_nonneg (sq_nonneg _) (AHH.edgeError_nonneg p x 0)

/-- Manuscript-form sharp Gaussian upper edge: the state denominator is
literally 2h and the real signs range over {-1,1}. -/
theorem paperGaussian_expectation_upper_edge (p : ℕ → ℕ) {x : ℝ}
    (hx : 0 < x)
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    (∀ h, 0 ≤ AHH.edgeError p x h) ∧
    AHH.edgeError p x =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    (∀ (h : ℕ) (s t : ℝ), (s = -1 ∨ s = 1) → (t = -1 ∨ t = 1) →
      (∫ z, ‖AHHAlgebraBridges.cMatrixCLM
          (paperComplexCovariance (p h) h s t z)‖ ∂fourGaussianLaw (p h) h) ≤
        (1 + Real.sqrt x) ^ 2 + AHH.edgeError p x h) := by
  have he := normalizedGaussian_all_signs_expectation_upper_edge p hx hp
  refine ⟨he.1, he.2.1, ?_⟩
  intro h s t hs ht
  obtain ⟨b, rfl⟩ := exists_bool_sign s hs
  obtain ⟨c, rfl⟩ := exists_bool_sign t ht
  simpa only [paperComplexCovariance_eq_actual] using he.2.2 h b c

end AHHGaussian

namespace AHHRadial

/-- The actual Haar product-state ensemble inherits the same sharp edge via
the proved radial Jensen comparison and the actual Gaussian moment estimate. -/
theorem normalizedHaar_expectation_upper_edge (p : ℕ → ℕ) {x : ℝ}
    (hx : 0 < x)
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    (∀ h, 0 ≤ AHH.edgeError p x h) ∧
    AHH.edgeError p x =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    (∀ h : ℕ,
      (∫ d, unitCovarianceNorm (p h) h d ∂directionsLaw (p h) h) ≤
        (1 + Real.sqrt x) ^ 2 + AHH.edgeError p x h) := by
  have he := AHHGaussian.normalizedGaussian_expectation_upper_edge p hx hp
  refine ⟨he.1, he.2.1, ?_⟩
  intro h
  by_cases hh : 0 < h
  · exact (haar_expected_norm_le_actualGaussian (p h) h hh true true).trans (he.2.2 h)
  · have hz : h = 0 := by omega
    subst h
    have hn (d : Directions (p 0) 0) : unitCovarianceNorm (p 0) 0 d = 0 := by
      unfold unitCovarianceNorm
      rw [show unitCovariance (p 0) 0 d = 0 from Subsingleton.elim _ _, norm_zero]
    simp only [hn, integral_zero]
    exact add_nonneg (sq_nonneg _) (AHH.edgeError_nonneg p x 0)

end AHHRadial

#print axioms AHHGaussian.normalizedGaussian_expectation_upper_edge
#print axioms AHHRadial.normalizedHaar_expectation_upper_edge

#print axioms AHHGaussian.normalizedGaussian_all_signs_expectation_upper_edge

#print axioms AHHGaussian.paperGaussian_expectation_upper_edge
