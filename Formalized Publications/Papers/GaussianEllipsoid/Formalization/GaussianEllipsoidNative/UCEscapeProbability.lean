import UCEscapeExpectation

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle
namespace UCEscape

variable {J : Type} [Fintype J] [Nonempty J] [MetricSpace J] [DiscreteTopology J]
  {n d r : ℕ}

theorem projectedEscape_lower_tail (hd : 0 < d) (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (a t : ℝ) (ht : 0 < t)
    (hmargin : a+t ≤ (1-ε)*Real.sqrt r*
      (1-(Fintype.card J : ℝ)*Real.exp (-ε^2*(r:ℝ)/8)) - Real.sqrt ((d:ℝ)*(d+1)/4)) :
    (sampleLaw n d).real {X | projectedEscape (d := d) U X ≤ a} ≤ Real.pi^2/(8*t^2) := by
  let m := ∫ X, projectedEscape (d := d) U X ∂sampleLaw n d
  have hm : a+t ≤ m := hmargin.trans (projectedEscape_mean_lower hd hr U ε hε hε1)
  have hLip : LipschitzWith 1 (fun X => projectedEscape (d := d) U X-m) := by
    apply LipschitzWith.of_dist_le_mul
    intro X Y
    have h := (projectedEscape_lipschitz hd U).dist_le_mul X Y
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right] using h
  have hi := GaussianVariance.lipschitz_sq_integrable hLip
  have hv := GaussianVariance.lipschitz_gaussian_variance_le (projectedEscape_lipschitz hd U)
  rw [variance_eq_integral (projectedEscape_lipschitz hd U).continuous.measurable.aemeasurable] at hv
  have hsub : {X | projectedEscape (d := d) U X ≤ a} ⊆
      {X | t^2 ≤ (projectedEscape (d := d) U X-m)^2} := by
    intro X hX
    change projectedEscape (d := d) U X ≤ a at hX
    change t^2 ≤ (projectedEscape (d := d) U X-m)^2
    have hg : t ≤ m-projectedEscape (d := d) U X := by linarith
    have hsq := pow_le_pow_left₀ ht.le hg 2
    nlinarith
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun X => sq_nonneg (projectedEscape (d := d) U X-m)) hi (t^2)
  have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := sampleLaw n d) hsub) (sq_nonneg t)
  have hbound : (sampleLaw n d).real {X | projectedEscape (d := d) U X ≤ a} ≤ (Real.pi^2/8)/t^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    change (∫ X, (projectedEscape (d := d) U X-m)^2 ∂sampleLaw n d) ≤ Real.pi^2/8 at hv
    nlinarith
  convert hbound using 1 <;> field_simp <;> ring

#print axioms projectedEscape_lower_tail
end UCEscape
