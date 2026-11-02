import CanonicalDimensionCompression

noncomputable section
open MeasureTheory Filter GaussianEllipsoid GaussianMixedNormHelpers
open scoped BigOperators Topology
namespace GaussianEllipsoidCandidate

/-- The paper's uniform sparse nuclear event in any actual row dimension. -/
def multiscaleGoodDimension (d n h : ℕ) (K : ℝ) :
    Set (Fin n → Euclid h × Euclid h) :=
  {X | ∀ u : Fin n → ℝ,
    ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
    multiscaleConstant K*Real.sqrt d*coefficientMass u ≤ scaledBilinearNuclear d u X}

theorem multiscaleGoodDimension_even_eq (d n : ℕ) (K : ℝ) :
    multiscaleGoodDimension d n (2*(d/4)) K = actualMultiscaleGood d n K := by
  ext X
  rfl

theorem multiscaleGoodDimension_isClosed (d n h : ℕ) (K : ℝ) :
    IsClosed (multiscaleGoodDimension d n h K) := by
  unfold multiscaleGoodDimension
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro u
  by_cases hs : ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d
  · have hc : IsClosed {X : Fin n → Euclid h × Euclid h |
        multiscaleConstant K*Real.sqrt d*coefficientMass u ≤ scaledBilinearNuclear d u X} :=
      isClosed_le continuous_const (continuous_scaledBilinearNuclear (h:=h) d u)
    simpa [hs] using hc
  · simp [hs]

theorem multiscaleGoodDimension_probability_mono (d n k h : ℕ) (hkh : k ≤ h) (K : ℝ) :
    (gaussianBilinearSampleLaw (Fin n) k k).real (multiscaleGoodDimension d n k K) ≤
      (gaussianBilinearSampleLaw (Fin n) h h).real (multiscaleGoodDimension d n h K) := by
  let e : Fin k ↪ Fin h := Fin.castLEEmb hkh
  let U := ContinuousLinearMap.adjoint (coordinateEmbedding e)
  have hU : U ∘L ContinuousLinearMap.adjoint U = ContinuousLinearMap.id ℝ _ := by
    simpa only [U, ContinuousLinearMap.adjoint_adjoint] using coordinateEmbedding_adjoint_comp e
  have hUnorm : ‖U‖ ≤ 1 := by simpa [U] using coordinateEmbedding_norm_le_one e
  have hp := compressCanonicalRows_preserving (n:=n) U hU
  have hmeas := (multiscaleGoodDimension_isClosed d n k K).measurableSet
  rw [← hp.measureReal_preimage hmeas.nullMeasurableSet]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro X hX
  intro u hu
  exact (hX u hu).trans (scaledBilinearNuclear_compress_le U hUnorm d u X)

/-- Paper Section7 main multiscale theorem in h=floor(d/2), with its explicit
constant and actual Gaussian law. The old even-half event is transported by
proved coordinate marginal invariance and nuclear compression. -/
theorem paper_multiscale_uniform_good_tendsto_one (A K : ℝ)
    (hA : 0 < A) (hK : 0 < K) (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) :
    Tendsto (fun d => (gaussianBilinearSampleLaw (Fin (n d)) (d/2) (d/2)).real
      (multiscaleGoodDimension d (n d) (d/2) K)) atTop (𝓝 1) := by
  have hsmall := actual_multiscale_uniform_good_tendsto_one A K hA hK.le n hn
  have hlower : ∀ d : ℕ,
      (gaussianBilinearSampleLaw (Fin (n d)) (2*(d/4)) (2*(d/4))).real
        (actualMultiscaleGood d (n d) K) ≤
      (gaussianBilinearSampleLaw (Fin (n d)) (d/2) (d/2)).real
        (multiscaleGoodDimension d (n d) (d/2) K) := by
    intro d
    rw [← multiscaleGoodDimension_even_eq]
    exact multiscaleGoodDimension_probability_mono d (n d) (2*(d/4)) (d/2) (by omega) K
  have hupper : ∀ d : ℕ,
      (gaussianBilinearSampleLaw (Fin (n d)) (d/2) (d/2)).real
        (multiscaleGoodDimension d (n d) (d/2) K) ≤ 1 := by
    intro d
    exact measureReal_le_one
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hsmall tendsto_const_nhds hlower hupper
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_multiscale_uniform_good_tendsto_one
