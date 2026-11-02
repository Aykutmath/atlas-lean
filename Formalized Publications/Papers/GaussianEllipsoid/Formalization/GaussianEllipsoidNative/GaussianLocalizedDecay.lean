import GaussianLocalizedProbability
import LocalizedEntropyDecay

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianEllipsoid.SmallBall

namespace GaussianEllipsoid.Localized

/-- Explicit exponential probability bound for the full homogeneous localized
event. Both the Gaussian estimate and coefficient entropy are discharged. -/
theorem gaussian_localized_exp_decay {α A B β K L : ℝ} {d n : ℕ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K) (hL : 0 < L)
    (hd : max 12 (entropyCutoff α A B β K L) ≤ d)
    (hn : (n:ℝ) ≤ α*(d:ℝ)^2) :
    (bilinearGaussianSampleLaw (2*(d/4)) n).real
      (homogeneousBad (localizedOperator d (2*(d/4)) n)
          A β B K (entropyScale α B β L) d ∩
        frobeniusContinuity (localizedOperator d (2*(d/4)) n) L d) ≤
      Real.exp (-(d:ℝ)^2) := by
  have hd12 : 12 ≤ d := (le_max_left _ _).trans hd
  have hcut : entropyCutoff α A B β K L ≤ d := (le_max_right _ _).trans hd
  have hc : 0 < entropyScale α B β L := Real.exp_pos _
  apply (gaussian_localized_even_finite_probability d n hd12 hA.le hβ hB.le hL hc).trans
  simpa only [pow_two, Nat.cast_add, Nat.cast_one] using
    localized_entropy_min_floor_le hα hα' hA hB hβ hK hL hcut hn

/-- Full unconditional Section 6 conclusion: fixed positive small-coordinate
scale and exponential rate, valid for every n≤αd² once d is large enough. -/
theorem exists_gaussian_localized_exp_decay {α A B β K L : ℝ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K) (hL : 0 < L) :
    ∃ c γ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < γ ∧ ∃ d₀ : ℕ,
      ∀ d n : ℕ, d₀ ≤ d → (n:ℝ) ≤ α*(d:ℝ)^2 →
      (bilinearGaussianSampleLaw (2*(d/4)) n).real
        (homogeneousBad (localizedOperator d (2*(d/4)) n) A β B K c d ∩
          frobeniusContinuity (localizedOperator d (2*(d/4)) n) L d) ≤
        Real.exp (-γ*(d:ℝ)^2) := by
  obtain ⟨_,_,_,hc,hc1,_⟩ := entropy_constants hα hα' hA hB hβ hL
  refine ⟨entropyScale α B β L,1,hc,hc1,by norm_num,
    max 12 (entropyCutoff α A B β K L),?_⟩
  intro d n hd hn
  simpa using gaussian_localized_exp_decay hα hα' hA hB hβ hK hL hd hn

end GaussianEllipsoid.Localized

#print axioms GaussianEllipsoid.Localized.gaussian_localized_exp_decay
#print axioms GaussianEllipsoid.Localized.exists_gaussian_localized_exp_decay
