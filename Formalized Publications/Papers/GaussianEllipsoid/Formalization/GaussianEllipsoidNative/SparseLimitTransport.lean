import MixedNormCoefficient

noncomputable section
set_option synthInstance.maxSize 1000
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoidCandidate
open GaussianEllipsoidFinalPassage GaussianTensorMoments
open scoped Topology BigOperators
namespace GaussianEllipsoidStandalone

/-- This event is the literal all-support sparse lower bound at the required
quantitative coefficient, before any probability theorem is applied. -/
def canonicalSparseGood (n r d : ℕ) : Set (Fin n → Euclid r × Euclid r) :=
  {X | ∀ u : Fin n → ℝ,
    ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ (1/numericalEta^2)*(d:ℝ) →
    fixedSparseCoefficient*Real.sqrt d*(∑ i, |u i|) ≤
      spectralNuclearNorm (operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X))}

theorem canonicalSparseGood_isClosed (n r d : ℕ) : IsClosed (canonicalSparseGood n r d) := by
  have heq : canonicalSparseGood n r d = ⋂ u : Fin n → ℝ,
      ⋂ (_ : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ (1/numericalEta^2)*(d:ℝ)),
      {X | fixedSparseCoefficient*Real.sqrt d*(∑ i, |u i|) ≤
        spectralNuclearNorm (operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X))} := by
    ext X; simp [canonicalSparseGood]
  rw [heq]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro _
  apply isClosed_le continuous_const
  exact (continuous_spectralNuclear r r).comp ((continuous_operatorFrobenius r r).comp
    (by simpa only [Pi.smul_apply] using!
      ((continuous_bilinearSynthesis n r u).const_smul ((Real.sqrt (d : ℝ))⁻¹))))

theorem flatSparseBad_eq_preimage (n r d : ℕ) : flatSparseBad n r d =
    (tensorToCanonicalRows n r) ⁻¹' (canonicalSparseGood n r d)ᶜ := by
  classical
  ext z
  constructor
  · rintro ⟨I,u,hI,hu,hbad⟩ hGood
    have hs : (Finset.univ.filter fun i => u i ≠ 0) ⊆ I := by
      intro i hi
      by_contra hn
      exact (Finset.mem_filter.mp hi).2 (hu i hn)
    have hcard : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤
        (1/numericalEta^2)*(d:ℝ) := by
      have hc : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ (I.card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hs)
      calc
        _ ≤ (I.card:ℝ) := hc
        _ ≤ (d:ℝ)/numericalEta^2 := hI
        _ = _ := by ring
    have hg := hGood (fun i => u i) hcard
    rw [flat_bilinear_eq_canonical] at hbad
    exact (not_lt_of_ge hg) hbad
  · intro hz
    change ¬∀ u : Fin n → ℝ,
      ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ (1/numericalEta^2)*(d:ℝ) →
      fixedSparseCoefficient*Real.sqrt d*(∑ i, |u i|) ≤
        spectralNuclearNorm (operatorFrobenius
          ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u (tensorToCanonicalRows n r z))) at hz
    push_neg at hz
    obtain ⟨u,hcard,hbad⟩ := hz
    refine ⟨Finset.univ.filter (fun i => u i ≠ 0),asCoeff u,?_,?_,?_⟩
    · convert hcard using 1 <;> ring
    · intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, asCoeff, WithLp.ofLp_toLp] using! hi
    · rw [flat_bilinear_eq_canonical]
      exact hbad

theorem flatSparseBad_probability (n r d : ℕ) :
    (tensorGaussianLaw n r).real (flatSparseBad n r d) =
      (gaussianBilinearSampleLaw (Fin n) r r).real (canonicalSparseGood n r d)ᶜ := by
  rw [flatSparseBad_eq_preimage]
  exact (tensorToCanonicalRows_preserving n r).measureReal_preimage
    (canonicalSparseGood_isClosed n r d).measurableSet.compl.nullMeasurableSet

end GaussianEllipsoidStandalone
