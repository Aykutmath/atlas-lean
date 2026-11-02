import MixedNormCoefficient
import GaussianGoodEventLimit
import AspectRatioLimit

/-!
A fully explicit Euclidean/nuclear standalone analogue of the supplied
MixedNormBody and MixedNormBound. This is not a declaration in the unavailable
GaussianEllipsoid project. The exact adapter needs Basic.lean and MixedNormAsm.lean.
The final unconditional theorem is assembled separately from the actual sparse
estimate; the helper in this file openly records its one remaining input.
-/
noncomputable section
set_option synthInstance.maxSize 1000
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoidCandidate
open GaussianMixedNormHelpers GaussianEllipsoidFinalPassage GaussianTensorMoments
open scoped ENNReal Topology BigOperators
namespace GaussianEllipsoidStandalone

abbrev Sample (d n : ℕ) := Fin n → Euclid d

def gaussianSampleLaw (d n : ℕ) : Measure (Sample d n) :=
  Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))

def dimensionRatio (n : ℕ → ℕ) (d : ℕ) : ℝ≥0∞ := (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2

/-- Literal d⁻¹ᐟ² centered quadratic synthesis, represented in the genuine
finite-dimensional Euclidean operator/Frobenius space. -/
def centeredAdjoint {d n : ℕ} (X : Sample d n) (y : Fin n → ℝ) : FrobeniusMatrix d d :=
  operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • centeredRankOneSynthesis y X)

def MixedNormBody (n : ℕ → ℕ) (δ η c : ℝ)
    (G : ∀ d, Set (Sample d (n d))) : Prop :=
  0 < η ∧ η < 1 ∧ 0 < c ∧
  limsup (fun d => ((gaussianSampleLaw d (n d)) (G d)ᶜ).toReal) atTop ≤ δ ∧
  ∀ d, ∀ X ∈ G d, ∀ y : Fin (n d) → ℝ, (∑ i, y i) = 0 →
    c * mixedNorm η d (n d) y ≤ spectralNuclearNorm (centeredAdjoint X y)

def MixedNormBound : Prop :=
  ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
    limsup (dimensionRatio n) atTop < (1/4:ℝ≥0∞) →
    ∀ δ > 0, ∃ η c : ℝ, ∃ G : ∀ d, Set (Sample d (n d)),
      MixedNormBody n δ η c G

/-- Transfer the already proved flat mixed estimate to the full sample law.
This gives measurable events, limsup exactly zero, and the stronger all-y bound. -/
theorem full_mixed_events_of_flat_limit (n : ℕ → ℕ) {c : ℝ}
    (hc : 0 < c)
    (hlim : Tendsto (fun d => (tensorGaussianLaw (n d) (2*(d/4))).real
      (flatMixedBad (n d) (2*(d/4)) d numericalEta c)) atTop (𝓝 0)) :
    ∃ G : ∀ d, Set (Sample d (n d)),
      (∀ d, MeasurableSet (G d)) ∧
      (∀ d, d < 4 → G d = ∅) ∧
      limsup (fun d => ((gaussianSampleLaw d (n d)) (G d)ᶜ).toReal) atTop = 0 ∧
      ∀ d, ∀ X ∈ G d, ∀ y : Fin (n d) → ℝ,
        c*mixedNorm numericalEta d (n d) y ≤ spectralNuclearNorm (centeredAdjoint X y) := by
  classical
  let E (d : ℕ) := (flatMixedBad (n d) (evenHalfDim d) d numericalEta c)ᶜ
  have hE (d : ℕ) : MeasurableSet (E d) := (flatMixedBad_measurable _ _ _ _ _).compl
  have hb : ∀ᶠ d in atTop, ∀ z ∈ E d, ∀ y : Fin (n d) → ℝ,
      c*mixedNorm numericalEta d (n d) y ≤ spectralNuclearNorm
        (gaussianBilinearOperator (n d) (evenHalfDim d) d z
          ((MeasurableEquiv.toLp 2 ((Fin (n d)) → ℝ)) y)) := by
    apply Eventually.of_forall
    intro d z hz y
    apply le_of_not_gt
    intro hbad
    exact hz ⟨y,hbad⟩
  have hl : Tendsto (fun d => ((tensorGaussianLaw (n d) (evenHalfDim d)) (E d)ᶜ).toReal)
      atTop (𝓝 0) := by
    have hEc (d : ℕ) : (E d)ᶜ =
        flatMixedBad (n d) (evenHalfDim d) d numericalEta c := by
      ext z
      change (¬¬ (z ∈ flatMixedBad (n d) (evenHalfDim d) d numericalEta c)) ↔
        (z ∈ flatMixedBad (n d) (evenHalfDim d) d numericalEta c)
      exact not_not
    apply hlim.congr'
    exact Eventually.of_forall (fun d =>
      congrArg ENNReal.toReal (congrArg (tensorGaussianLaw (n d) (evenHalfDim d))
        (hEc d).symm))
  obtain ⟨G,hG,hGlim,hGb⟩ := eventual_even_tensor_good_event_transfer n E hE
    (fun d y => c*mixedNorm numericalEta d (n d) y) hb hl
  let G' (d : ℕ) := if 4 ≤ d then G d else ∅
  refine ⟨G',?_,?_,?_,?_⟩
  · intro d
    dsimp [G']
    split_ifs
    · exact hG d
    · exact MeasurableSet.empty
  · intro d hd
    simp [G', show ¬4 ≤ d by omega]
  · have heq : (fun d => ((gaussianSampleLaw d (n d)) (G' d)ᶜ).toReal) =ᶠ[atTop]
        (fun d => ((gaussianSampleLaw d (n d)) (G d)ᶜ).toReal) := by
      filter_upwards [eventually_ge_atTop 4] with d hd
      simp [G',hd]
    rw [limsup_congr heq]
    exact hGlim
  · intro d X hX y
    by_cases hd : 4 ≤ d
    · exact hGb d X (by simpa [G',hd] using hX) y
    · simp [G',hd] at hX

/-- Honest conditional final helper, awaiting only the actual uniform sparse
limit. It does not assume clipping, continuity, small-coordinate probability,
Gaussian-law identification, or nuclear compression. -/
theorem mixedNormBody_of_sparse_limit (n : ℕ → ℕ)
    (haspect : limsup (dimensionRatio n) atTop < (1/4:ℝ≥0∞))
    (hSparse : Tendsto (fun d => (tensorGaussianLaw (n d) (2*(d/4))).real
      (flatSparseBad (n d) (2*(d/4)) d)) atTop (𝓝 0)) :
    ∀ δ > 0, ∃ η c : ℝ, ∃ G : ∀ d, Set (Sample d (n d)),
      MixedNormBody n δ η c G ∧ (∀ d, MeasurableSet (G d)) ∧ (∀ d, d < 4 → G d = ∅) := by
  obtain ⟨α,hα,hα',hn⟩ := exists_eventual_quadratic_bound n haspect
  obtain ⟨c,hc,hlim⟩ := flat_mixed_limit_of_sparse_limit hα hα' n hn hSparse
  obtain ⟨G,hG,hGsmall,hGlim,hGb⟩ := full_mixed_events_of_flat_limit n hc hlim
  intro δ hδ
  refine ⟨numericalEta,c,G,?_,hG,hGsmall⟩
  refine ⟨numerical_eta_range.1,numerical_eta_range.2.1,hc,?_,?_⟩
  · rw [hGlim]
    exact hδ.le
  · intro d X hX y _
    exact hGb d X hX y

end GaussianEllipsoidStandalone
