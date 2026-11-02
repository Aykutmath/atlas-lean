import GaussianExtractedRowsLaw
import GaussianLateDriver
import BilinearSynthesis

noncomputable section
open MeasureTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoid GaussianEllipsoid.ProjectedClusters
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoidCandidate

/-- The canonical pair-row observable and the tensor-coordinate observable
are exactly the same matrix, with the specified d⁻¹ᐟ² normalization. -/
theorem scaled_bilinearSynthesis_tensorToCanonicalRows (n h d : ℕ)
    (u : Fin n → ℝ) (z : GaussianEntries n h × GaussianEntries n h) :
    operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ •
      bilinearSynthesis u (tensorToCanonicalRows n h z)) =
    gaussianBilinearOperator n h d z ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) u) := by
  ext j i
  change (Real.sqrt (d:ℝ))⁻¹ *
      operatorFrobenius (bilinearSynthesis u (tensorToCanonicalRows n h z)) j i =
    frobeniusToMatrix (gaussianBilinearOperator n h d z
      ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) u)) i j
  rw [bilinearSynthesis_entry, gaussianBilinearOperator_apply]
  rfl

/-- Borel measurability of the exact normalized nuclear observable. -/
theorem measurable_scaled_bilinear_nuclear {n h d : ℕ} (u : Fin n → ℝ) :
    Measurable (fun X : Fin n → Euclid h × Euclid h =>
      spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X))) :=
  (continuous_spectralNuclear h h).measurable.comp
    ((continuous_operatorFrobenius h h).measurable.comp
      (by simpa only [Pi.smul_def] using
        (measurable_bilinearSynthesis (r:=h) (q:=h) u).const_smul ((Real.sqrt (d:ℝ))⁻¹)))

/-- Exact equality of the actual Gaussian probabilities of a nuclear sublevel
in the canonical pair-row and tensor-coordinate presentations. -/
theorem canonical_bilinear_nuclear_sublevel_probability (n h d : ℕ)
    (u : Fin n → ℝ) (a : ℝ) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X)) ≤ a} =
    (tensorGaussianLaw n h).real
      {z | spectralNuclearNorm (gaussianBilinearOperator n h d z
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) u)) ≤ a} := by
  have hE : MeasurableSet {X : Fin n → Euclid h × Euclid h |
      spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X)) ≤ a} :=
    measurableSet_le (measurable_scaled_bilinear_nuclear (d:=d) u) measurable_const
  rw [← (tensorToCanonicalRows_preserving n h).measureReal_preimage hE.nullMeasurableSet]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, scaled_bilinearSynthesis_tensorToCanonicalRows]

/-- Macroscopic late-driver bound in the exact canonical Gaussian row law.
All coefficients off the driver remain arbitrary. -/
theorem canonical_macroscopic_late_driver_smallball {n d : ℕ}
    (S : Finset (Fin n)) (w : Fin n → ℝ) {c₀ K ℓ : ℝ}
    (hc₀ : 0 < c₀) (hlarge : 64 ≤ min c₀ 1 * (d:ℝ))
    (hlowSize : c₀*(d:ℝ) ≤ S.card) (hupSize : (S.card:ℝ) ≤ K*(d:ℝ))
    (hℓ : 0 < ℓ) (hlower : ∀ i ∈ S, ℓ ≤ |w i|)
    (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      {X | spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis w X)) ≤
        (1/1048576:ℝ) / Real.sqrt (max K 1) * Real.sqrt d * (∑ i ∈ S, |w i|)} ≤
      Real.exp (-(min c₀ 1)*(d:ℝ)^2/1024) := by
  rw [canonical_bilinear_nuclear_sublevel_probability]
  exact GaussianPairedBlocks.gaussian_macroscopic_late_driver_smallball_even_half
    S w hc₀ hlarge hlowSize hupSize hℓ hlower hupper

end GaussianEllipsoidCandidate
