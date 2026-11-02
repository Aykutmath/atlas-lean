import BMBadEventTail
import BMPSDGaussianVariance

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal Topology
open GaussianEllipsoid GaussianTensorMoments MeasureTheory ProbabilityTheory Filter
namespace BMGeometry

/-- Fully unconditional finite-d Gaussian width lower bound for BM's bounded-condition cone. -/
theorem conditionedWidth_gaussian_lower {d : ℕ} (hd : 0 < d) {ε κ δ : ℝ}
    (hdV : 16*(Real.pi^2/8) ≤ (d:ℝ)^2) (hε : 0 < ε) (hκ : 1 ≤ κ)
    (hκε : 12+ε ≤ κ*ε) (hδ : 0 < δ) :
    Real.sqrt ((d:ℝ)*(d+1)/4-Real.pi^2/8) - 49*ε*d - δ*(d+1)/2 -
      (d/δ)*(144*(Real.pi^2/8)/(d:ℝ)^2+2*Real.exp (-2*(d:ℝ))) ≤ conditionedWidth d κ := by
  exact conditionedWidth_explicit_lower hd (by positivity) hdV hε hκ hκε hδ
    (gaussianPSDSupportRaw_centered_sq_le d)

def normalizedWidthLower (V ε δ : ℝ) (d : ℕ) : ℝ :=
  Real.sqrt ((1+1/(d:ℝ))/4 - V/(d:ℝ)^2) - 49*ε - δ*(1+1/(d:ℝ))/2 -
    (1/δ)*(144*V/(d:ℝ)^2 + 2*Real.exp (-2*(d:ℝ)))

theorem normalizedWidthLower_tendsto (V ε δ : ℝ) :
    Tendsto (normalizedWidthLower V ε δ) atTop (𝓝 ((1/2:ℝ)-49*ε-δ/2)) := by
  have hi : Tendsto (fun d : ℕ => 1/(d:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hVsq : Tendsto (fun d : ℕ => V/(d:ℝ)^2) atTop (𝓝 0) := by
    convert! (tendsto_const_nhds.mul (hi.pow 2) :
      Tendsto (fun d : ℕ => V*(1/(d:ℝ))^2) atTop (𝓝 (V*0^2))) using 1
    · ext d; simp [div_eq_mul_inv, inv_pow]
    · simp
  have h144sq : Tendsto (fun d : ℕ => 144*V/(d:ℝ)^2) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hVsq.const_mul 144
  have hexp : Tendsto (fun d : ℕ => Real.exp (-2*(d:ℝ))) atTop (𝓝 0) := by
    have hD : Tendsto (fun d : ℕ => 2*(d:ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<2) tendsto_natCast_atTop_atTop
    simpa only [neg_mul, Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hD
  have harg : Tendsto (fun d : ℕ => (1+1/(d:ℝ))/4 - V/(d:ℝ)^2) atTop (𝓝 (1/4:ℝ)) := by
    convert! ((tendsto_const_nhds.add hi).div_const 4).sub hVsq using 1 <;> norm_num
  have h := ((harg.sqrt.sub_const (49*ε)).sub
    ((((tendsto_const_nhds (x := (1:ℝ))).add hi).const_mul δ).div_const 2)).sub
    ((h144sq.add (hexp.const_mul 2)).const_mul (1/δ))
  convert! h using 1
  norm_num

theorem normalizedWidthLower_le_width {d : ℕ} (hd : 0 < d) {ε κ δ : ℝ}
    (hdV : 16*(Real.pi^2/8) ≤ (d:ℝ)^2) (hε : 0 < ε) (hκ : 1 ≤ κ)
    (hκε : 12+ε ≤ κ*ε) (hδ : 0 < δ) :
    normalizedWidthLower (Real.pi^2/8) ε δ d ≤ conditionedWidth d κ / d := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hQ : 0 ≤ (d:ℝ)*(d+1)/4 - Real.pi^2/8 := by nlinarith [sq_nonneg Real.pi]
  have hsqrt : Real.sqrt ((1+1/(d:ℝ))/4 - (Real.pi^2/8)/(d:ℝ)^2) =
      Real.sqrt ((d:ℝ)*(d+1)/4-Real.pi^2/8)/(d:ℝ) := by
    have heq : (1+1/(d:ℝ))/4 - (Real.pi^2/8)/(d:ℝ)^2 =
        ((d:ℝ)*(d+1)/4-Real.pi^2/8)/(d:ℝ)^2 := by field_simp
    rw [heq, Real.sqrt_div hQ, Real.sqrt_sq hd'.le]
  have h := div_le_div_of_nonneg_right (conditionedWidth_gaussian_lower hd hdV hε hκ hκε hδ) hd'.le
  unfold normalizedWidthLower
  rw [hsqrt]
  convert! h using 1 <;> field_simp <;> ring

/-- BM Lemma 3.5 in the exact form needed below the threshold: one dimension-independent
condition number makes the normalized cone width arbitrarily close to 1/2. No Wigner law is used. -/
theorem exists_conditionNumber_eventually_width_lower {η : ℝ} (hη : 0 < η) :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∀ᶠ d : ℕ in atTop, (1/2:ℝ)-η < conditionedWidth d κ / d := by
  let ε : ℝ := η/196
  let δ : ℝ := η/2
  let κ : ℝ := 1+12/ε
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hκ : 1 ≤ κ := by
    dsimp [κ]
    have hh := div_nonneg (by norm_num : (0:ℝ) ≤ 12) hε.le
    linarith
  have hκε : 12+ε ≤ κ*ε := by dsimp [κ]; field_simp; linarith
  refine ⟨κ,hκ,?_⟩
  have hlim := normalizedWidthLower_tendsto (Real.pi^2/8) ε δ
  have hgap : (1/2:ℝ)-η < (1/2:ℝ)-49*ε-δ/2 := by dsimp [ε,δ]; linarith
  have hlarge : ∀ᶠ d : ℕ in atTop, (1/2:ℝ)-η < normalizedWidthLower (Real.pi^2/8) ε δ d :=
    hlim.eventually (Ioi_mem_nhds hgap)
  have hD : ∀ᶠ d : ℕ in atTop, max 1 (16*(Real.pi^2/8)) ≤ (d:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hlarge,hD] with d hdlarge hdD
  have hd1 : (1:ℝ) ≤ d := (le_max_left _ _).trans hdD
  have hd : 0 < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hd1)
  have hdV : 16*(Real.pi^2/8) ≤ (d:ℝ)^2 := by
    have hh := (le_max_right (1:ℝ) (16*(Real.pi^2/8))).trans hdD
    nlinarith
  exact hdlarge.trans_le (normalizedWidthLower_le_width hd hdV hε hκ hκε hδ)

end BMGeometry
