import BMWidthLower

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
open GaussianEllipsoid GaussianTensorMoments MeasureTheory ProbabilityTheory
namespace BMGeometry

/-- No sharp random-matrix asymptotic is needed: a quarter-net gives an explicit exp(-2d) tail. -/
theorem isotropicSymmetricOp_twelve_tail (d : ℕ) :
    (gaussianProductLaw (Fin d × Fin d)).real
      {x | 12*Real.sqrt d < ‖isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)‖} ≤
      2*Real.exp (-2*(d:ℝ)) := by
  have h := isotropicSymmetricOp_net_tail d (r := 6*Real.sqrt d) (by positivity)
  have heq : 2*(6*Real.sqrt d) = 12*Real.sqrt d := by ring
  rw [heq] at h
  apply h.trans
  have hsq := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  have hlog : Real.log 9 ≤ (8 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9)
    linarith
  have hpow : (9:ℝ)^(d+d) = Real.exp ((d+d:ℕ)*Real.log 9) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<9)]
  rw [hpow, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (d+d) : (0:ℝ) ≤ (d+d:ℕ))
  push_cast at hm ⊢
  nlinarith

theorem gaussianPSDCentered_integrable (d : ℕ) :
    Integrable (fun x => (gaussianPSDSupportRaw d x - psdWidth d)^2)
      (gaussianProductLaw (Fin d × Fin d)) := by
  have h := ((gaussianPSDSupportRaw_sq_integrable d).sub
    ((gaussianPSDSupportRaw_integrable d).const_mul (2*psdWidth d))).add (integrable_const ((psdWidth d)^2))
  convert! h using 1
  funext x
  change (gaussianPSDSupportRaw d x - psdWidth d)^2 =
    (gaussianPSDSupportRaw d x)^2 - 2*psdWidth d*gaussianPSDSupportRaw d x + (psdWidth d)^2
  ring

theorem psdWidth_ge_third {d : ℕ} (hd : 0 < d) {V : ℝ} (hV : 0 ≤ V) (hdV : 16*V ≤ (d:ℝ)^2)
    (hvar : (∫ x, (gaussianPSDSupportRaw d x - psdWidth d)^2
      ∂gaussianProductLaw (Fin d × Fin d)) ≤ V) : (d:ℝ)/3 ≤ psdWidth d := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hQ : 0 ≤ (d:ℝ)*(d+1)/4 - V := by nlinarith
  have h := psdWidth_lower_of_variance hvar
  have hm := (sq_le_sq₀ (Real.sqrt_nonneg _) (psdWidth_nonneg d)).mpr h
  rw [Real.sq_sqrt hQ] at hm
  have hn := psdWidth_nonneg d
  nlinarith

/-- A dimension-free variance bound makes the positive spectral energy macroscopic with
failure probability O(d^-2), with all Gaussian moments proved above. -/
theorem gaussianPSDSupport_quarter_tail {d : ℕ} (hd : 0 < d) {V : ℝ}
    (hV : 0 ≤ V) (hdV : 16*V ≤ (d:ℝ)^2)
    (hvar : (∫ x, (gaussianPSDSupportRaw d x - psdWidth d)^2
      ∂gaussianProductLaw (Fin d × Fin d)) ≤ V) :
    (gaussianProductLaw (Fin d × Fin d)).real {x | gaussianPSDSupportRaw d x < (d:ℝ)/4} ≤
      144*V/(d:ℝ)^2 := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hm := psdWidth_ge_third hd hV hdV hvar
  have hsub : {x | gaussianPSDSupportRaw d x < (d:ℝ)/4} ⊆
      {x | ((d:ℝ)/12)^2 ≤ (gaussianPSDSupportRaw d x-psdWidth d)^2} := by
    intro x hx
    change gaussianPSDSupportRaw d x < (d:ℝ)/4 at hx
    change ((d:ℝ)/12)^2 ≤ (gaussianPSDSupportRaw d x-psdWidth d)^2
    have hgap : (d:ℝ)/12 ≤ psdWidth d - gaussianPSDSupportRaw d x := by linarith
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (d:ℝ)/12) hgap 2
    nlinarith
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (fun x => sq_nonneg (gaussianPSDSupportRaw d x-psdWidth d)))
    (gaussianPSDCentered_integrable d) (((d:ℝ)/12)^2)
  have hmul := mul_le_mul_of_nonneg_left (measureReal_mono (μ := gaussianProductLaw (Fin d × Fin d)) hsub) (sq_nonneg ((d:ℝ)/12))
  apply (le_div_iff₀ (sq_pos_of_pos hd')).mpr
  nlinarith

theorem coneBadEvent_quarter_twelve_tail {d : ℕ} (hd : 0 < d) {V : ℝ}
    (hV : 0 ≤ V) (hdV : 16*V ≤ (d:ℝ)^2)
    (hvar : (∫ x, (gaussianPSDSupportRaw d x - psdWidth d)^2
      ∂gaussianProductLaw (Fin d × Fin d)) ≤ V) :
    (gaussianProductLaw (Fin d × Fin d)).real (coneBadEvent d (1/4) 12) ≤
      144*V/(d:ℝ)^2 + 2*Real.exp (-2*(d:ℝ)) := by
  apply (measureReal_union_le _ _).trans
  apply add_le_add
  · convert gaussianPSDSupport_quarter_tail hd hV hdV hvar using 1 <;> congr 2 <;> ext x <;> ring_nf
  · exact isotropicSymmetricOp_twelve_tail d

/-- Quantitative finite-dimensional substitute for BM Lemma 3.5. Only the generic Gaussian
variance bound remains an analysis input; the cone geometry and random-matrix estimates are actual. -/
theorem conditionedWidth_explicit_lower {d : ℕ} (hd : 0 < d) {V ε κ δ : ℝ}
    (hV : 0 ≤ V) (hdV : 16*V ≤ (d:ℝ)^2) (hε : 0 < ε) (hκ : 1 ≤ κ)
    (hκε : 12+ε ≤ κ*ε) (hδ : 0 < δ)
    (hvar : (∫ x, (gaussianPSDSupportRaw d x - psdWidth d)^2
      ∂gaussianProductLaw (Fin d × Fin d)) ≤ V) :
    Real.sqrt ((d:ℝ)*(d+1)/4-V) - 49*ε*d - δ*(d+1)/2 -
      (d/δ)*(144*V/(d:ℝ)^2+2*Real.exp (-2*(d:ℝ))) ≤ conditionedWidth d κ := by
  have h := conditionedWidth_lower_with_bad_mass hd (a := 1/4) (C := 12)
    (by norm_num) (by norm_num) hε hκ hκε hδ
  have hmean := psdWidth_lower_of_variance hvar
  have hbad := mul_le_mul_of_nonneg_left (coneBadEvent_quarter_twelve_tail hd hV hdV hvar)
    (div_nonneg (Nat.cast_nonneg d) hδ.le)
  norm_num at h
  nlinarith

end BMGeometry
