/- Newly reconstructed missing paper module, 2026-10-03.
   This is new source, not a recovered copy. Sharp Gaussian concentration is
   proved from actual-law covariance interpolation and smooth approximation. -/
import UCEscapeExpectation
import GaussianFiniteIndexConcentration

noncomputable section
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle
open scoped BigOperators InnerProductSpace
namespace UCEscape

variable {J : Type} [Fintype J] [Nonempty J] [MetricSpace J] [DiscreteTopology J]
  {n d r : ℕ}

lemma projectedEscape_nonneg (hd : 0 < d)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (X : Sample n d) :
    0 ≤ projectedEscape (d := d) U X := by
  letI : Nonempty ↥(psdUnit d) := (psdUnit_nonempty hd).to_subtype
  apply le_csInf (Set.range_nonempty _)
  rintro y ⟨p, rfl⟩
  exact norm_nonneg _

/-- The precise sharp lower tail about the actual expectation. -/
theorem projectedEscape_sharp_lower_tail (hd : 0 < d) (_hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (t : ℝ) (ht : 0 ≤ t) :
    (sampleLaw n d).real {X | projectedEscape (d := d) U X <
      (∫ Y, projectedEscape (d := d) U Y ∂sampleLaw n d)-t} ≤ Real.exp (-t^2/2) :=
  GaussianFiniteIndexConcentration.nonnegative_lipschitz_strict_lower_tail
    (projectedEscape_lipschitz hd U) (projectedEscape_nonneg hd U) ht

/-- The exact explicit finite-frame-family threshold, with unchanged constants. -/
theorem projectedEscape_explicit_sharp_lower_tail (hd : 0 < d) (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (sampleLaw n d).real {X | projectedEscape (d := d) U X <
      (1-ε)*Real.sqrt r*(1-(Fintype.card J : ℝ)*Real.exp (-ε^2*(r:ℝ)/8)) -
        Real.sqrt ((d:ℝ)*(d+1)/4)-t} ≤ Real.exp (-t^2/2) := by
  have hm := projectedEscape_mean_lower hd hr U ε hε hε1
  apply (measureReal_mono (μ := sampleLaw n d) (fun X hX =>
    lt_of_lt_of_le hX (sub_le_sub_right hm t))).trans
  exact projectedEscape_sharp_lower_tail hd hr U t ht

#print axioms projectedEscape_sharp_lower_tail
#print axioms projectedEscape_explicit_sharp_lower_tail
end UCEscape
