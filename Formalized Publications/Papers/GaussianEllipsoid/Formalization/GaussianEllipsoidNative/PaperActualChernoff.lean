import PaperChernoffOptimization
import PaperFullHalfLogDepth

noncomputable section
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers
open GaussianEllipsoid.PaperCanonicalPolar
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Actual canonical Gaussian cross sums satisfy the literal Markov infimum and
minimum-parameter bound once the separately proved pathwise variance bound is
substituted. The compensated expectation is discharged from the Gaussian model. -/
theorem paper_exact_cross_markov_infimum {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (V B x : ℝ) (hV : 0 < V) (hB : 0 < B) (hx : 0 ≤ x)
    (hcoef : ∀ i,|v i| ≤ B)
    (hvar : ∀ X : Fin N → Euclid q × Euclid r, exactPrefixVariance u v lo hi X ≤ V) :
    (gaussianBilinearSampleLaw (Fin N) q r).real {X | exactPrefixCross u v lo hi X ≤ -x} ≤
      (⨅ lam : Set.Icc (0:ℝ) ((1/Real.sqrt 2)/B), Real.exp (-lam.val*x+lam.val^2*V)) ∧
    (⨅ lam : Set.Icc (0:ℝ) ((1/Real.sqrt 2)/B), Real.exp (-lam.val*x+lam.val^2*V)) ≤
      Real.exp (-(1/4:ℝ)*min (x^2/V) ((1/Real.sqrt 2)*x/B)) := by
  apply paper_tail_from_random_compensator (gaussianBilinearSampleLaw (Fin N) q r)
    (exactPrefixCross u v lo hi) (exactPrefixVariance u v lo hi)
    (measurable_exactPrefixCross u v lo hi hlo) V B (1/Real.sqrt 2) x hV hB (by positivity) hx
  · intro lam hl hr
    apply paper_exact_polar_compensator u v lo hi hlo hsep B hB hcoef lam hl
    simpa only [div_div] using hr
  · exact Filter.Eventually.of_forall hvar

/-- All retained mass may lie in the sparse prefix. Then the future vector is
zero even if its total retained mass is positive. -/
theorem postprefixCoefficients_eq_zero_of_no_future {n : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ)
    (hp : groups.length ≤ p) : postprefixCoefficients u amp groups T p=0 := by
  funext i
  simp [postprefixCoefficients,postprefixSupport,Finset.Ico_eq_empty_of_le hp]

theorem actualExactCapturedCross_eq_zero_of_no_future {n d h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hreg : ∀ g ∈ groups,RegularRetainedGroup u amp T g) (hflat : groups.flatten.Nodup)
    (hp : groups.length ≤ p) (X : Fin n → Euclid h × Euclid h) :
    actualExactCapturedCross u amp ha groups T d p q hreg hflat X=0 := by
  simp [actualExactCapturedCross,postprefixCoefficients_eq_zero_of_no_future u amp groups T p hp,
    exactPrefixCross]

/-- Empty future cross sum: every positive lower-tail threshold has probability
zero, without interpreting real division by zero as an infinite MGF radius. -/
theorem paper_actual_zero_future_tail {n d h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hreg : ∀ g ∈ groups,RegularRetainedGroup u amp T g) (hflat : groups.flatten.Nodup)
    (hp : groups.length ≤ p) (x : ℝ) (hx : 0 < x) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | actualExactCapturedCross u amp ha groups T d p q hreg hflat X ≤ -x}=0 := by
  apply paper_zero_future_tail _ _ _ x hx
  exact Filter.Eventually.of_forall (actualExactCapturedCross_eq_zero_of_no_future u amp ha groups T p q hreg hflat hp)

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_exact_cross_markov_infimum
#print axioms GaussianEllipsoidCandidate.paper_actual_zero_future_tail
