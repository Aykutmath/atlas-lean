import UCEscapeProbability

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle
namespace UCEscape

/-- Dimension-uniform Gaussian escape with an explicit finite-size threshold.
All premises are numerical dimension/cardinality inequalities; the probability
and Gaussian comparison are fully proved in the preceding modules. -/
theorem projectedEscape_macroscopic_tail
    {J : Type} [Fintype J] [Nonempty J] [MetricSpace J] [DiscreteTopology J]
    {n d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n)
    (β ε c : ℝ) (hβ : 0 ≤ β) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1/2) (hc : 0 < c)
    (hrank : β*(d:ℝ)^2 ≤ r)
    (hmargin : 1/2+3*c ≤ (1-2*ε)*Real.sqrt β)
    (hdlarge : 1/4 ≤ c*(d:ℝ))
    (hcard : (Fintype.card J : ℝ)*Real.exp (-ε^2*(r:ℝ)/8) ≤ ε) :
    (sampleLaw n d).real {X | projectedEscape (d := d) U X ≤ c*d} ≤
      Real.pi^2/(8*c^2*(d:ℝ)^2) := by
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hdpos : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hs : Real.sqrt β*(d:ℝ) ≤ Real.sqrt (r:ℝ) := by
    have h := Real.sqrt_le_sqrt hrank
    rw [Real.sqrt_mul hβ, Real.sqrt_sq_eq_abs, abs_of_nonneg hd0] at h
    exact h
  have hw : Real.sqrt ((d:ℝ)*(d+1)/4) ≤ (d:ℝ)/2+1/4 := by
    have hnon : 0 ≤ (d:ℝ)*(d+1)/4 := by positivity
    nlinarith [Real.sq_sqrt hnon, Real.sqrt_nonneg ((d:ℝ)*(d+1)/4)]
  have hcoeff : 0 ≤ 1-2*ε := by linarith
  have hmean1 : (1-2*ε)*Real.sqrt r ≤
      (1-ε)*Real.sqrt r*(1-(Fintype.card J:ℝ)*Real.exp (-ε^2*(r:ℝ)/8)) := by
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_left hcard 1)
      (mul_nonneg (by linarith : 0 ≤ 1-ε) (Real.sqrt_nonneg (r:ℝ)))
    have hpos := mul_nonneg (sq_nonneg ε) (Real.sqrt_nonneg (r:ℝ))
    nlinarith
  have hdim := mul_le_mul_of_nonneg_right hmargin hd0
  have hnorm := mul_le_mul_of_nonneg_left hs hcoeff
  have hm : c*(d:ℝ)+c*(d:ℝ) ≤
      (1-ε)*Real.sqrt r*(1-(Fintype.card J:ℝ)*Real.exp (-ε^2*(r:ℝ)/8)) -
        Real.sqrt ((d:ℝ)*(d+1)/4) := by nlinarith
  have h := projectedEscape_lower_tail hd hr U ε hε (by linarith)
    (c*d) (c*d) (mul_pos hc hdpos) hm
  convert h using 1 <;> ring

#print axioms projectedEscape_macroscopic_tail
end UCEscape
