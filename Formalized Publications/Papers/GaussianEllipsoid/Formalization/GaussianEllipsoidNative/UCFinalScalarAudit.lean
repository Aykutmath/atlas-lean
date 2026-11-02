import UCPeelingSourceReduction
import UCMatrixRotation

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
namespace GaussianEllipsoid.UCFinalScalarAudit

/-- Exact scalar budget: the chosen perturbation spends less than a quarter
of the diffuse margin at the tail cutoff. -/
theorem tolerance_error {C δ c : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hc : 0 < c) :
    4*C*(δ*c/(16*(C+1))) < δ*c/4 := by
  have hden : 0 < 16*(C+1) := by positivity
  rw [← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith [mul_pos hδ hc]

/-- This is stronger than required: the rotated margin is below half the
scaled fixed-frame threshold. In particular no factor of rho was lost. -/
theorem rotated_budget {C δ c m m' ρ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hc : 0 < c) (hρ : δ < ρ)
    (hsmall : m < δ*c/4)
    (herr : |m'-m| ≤ 4*C*(δ*c/(16*(C+1)))) :
    m' < ρ*c/2 := by
  have he := tolerance_error hC hδ hc
  have hp := mul_lt_mul_of_pos_right hρ hc
  have hh := (abs_le.mp herr).2
  linarith

theorem source_constants {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    0 < UCPeelingSmallTail.tailCutoff a*c/(16*(UCUniformContinuity.continuityConstant a+1)) ∧
    0 < min UCPeelingSmallTail.peeledMargin (UCPeelingSmallTail.tailCutoff a*c/4) ∧
    min UCPeelingSmallTail.peeledMargin (UCPeelingSmallTail.tailCutoff a*c/4)
      ≤ UCPeelingSmallTail.peeledMargin ∧
    4*UCUniformContinuity.continuityConstant a*
        (UCPeelingSmallTail.tailCutoff a*c/(16*(UCUniformContinuity.continuityConstant a+1)))
      < UCPeelingSmallTail.tailCutoff a*c/4 := by
  have hδ := UCPeelingSmallTail.tailCutoff_pos ha
  have hC := UCUniformContinuity.continuityConstant_pos ha
  exact ⟨by positivity,
    lt_min UCPeelingSmallTail.peeledMargin_pos (by positivity),
    min_le_left _ _, tolerance_error hC hδ hc⟩

/-- Audits the actual conjugation and empirical centered-l1 normalization.
Both matrix arguments use the literal source conicMargin. -/
theorem conjugated_source_margin_lt {a c ρ : ℝ} (ha : 0 < a) (hc : 0 < c)
    {d n : ℕ} (hn : 0 < n) (x : Sample d n)
    (hCont : ‖UCContinuityGeometry.empiricalOperator x‖ ≤ UCUniformContinuity.continuityConstant a)
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (hO : ‖(O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))-1‖
      ≤ UCPeelingSmallTail.tailCutoff a*c/(16*(UCUniformContinuity.continuityConstant a+1)))
    (A : Square d) (hA : A.PosSemidef) (hF : frobeniusNorm A=1)
    (hρ : UCPeelingSmallTail.tailCutoff a < ρ)
    (hbad : conicMargin x A < min UCPeelingSmallTail.peeledMargin
      (UCPeelingSmallTail.tailCutoff a*c/4)) :
    conicMargin x (UCMatrixRotation.conjugate O A) < ρ*c := by
  have hC := UCUniformContinuity.continuityConstant_pos ha
  have hδ := UCPeelingSmallTail.tailCutoff_pos ha
  have hρc : 0 < ρ*c := mul_pos (hδ.trans hρ) hc
  have hdiff := UCMatrixRotation.conjugate_sub_frobenius_le O A
  rw [hF,mul_one] at hdiff
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left hO (by norm_num : (0:ℝ) ≤ 2))
  have herr := UCFixedRankGeometry.conicMargin_abs_sub_le hn x
    (UCMatrixRotation.conjugate O A) A
    (UCPeelingSmallTail.psd_transpose _ (UCMatrixRotation.conjugate_posSemidef O hA))
    (UCPeelingSmallTail.psd_transpose _ hA) (UCUniformContinuity.continuityConstant a) hCont
  have herr' : |conicMargin x (UCMatrixRotation.conjugate O A)-conicMargin x A| ≤
      4*UCUniformContinuity.continuityConstant a*
        (UCPeelingSmallTail.tailCutoff a*c/(16*(UCUniformContinuity.continuityConstant a+1))) := by
    have hh := mul_le_mul_of_nonneg_left hdiff' (show 0 ≤ 2*UCUniformContinuity.continuityConstant a by positivity)
    exact herr.trans (by nlinarith [hh])
  have hh := rotated_budget hC hδ hc hρ (hbad.trans_le (min_le_right _ _)) herr'
  linarith

/-- Three independent exponential contributions, including an extra copy of
the continuity exception, retain a positive quadratic rate after absorption. -/
theorem three_exponentials_absorption {a r C : ℝ} (ha : 0 < a) (hr : 0 < r) (hC : 0 < C) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, a*(d:ℝ)^2 ≤ n →
      Real.exp (-r*(n:ℝ)) + (Real.exp (-(n:ℝ)) + Real.exp (-C*(d:ℝ)^2))
        ≤ Real.exp (-q*(d:ℝ)^2) := by
  let Q := min (r*a) (min a C)
  have hQ : 0 < Q := lt_min (mul_pos hr ha) (lt_min ha hC)
  refine ⟨Q/2,by positivity,?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (4/Q),
    eventually_ge_atTop 1] with d hd hd1
  intro n hn
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd1
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hdSq : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hsize : 4 ≤ Q*(d:ℝ)^2 := by
    have hh := (div_le_iff₀ hQ).mp hd
    nlinarith [mul_le_mul_of_nonneg_left hdSq hQ.le]
  have hQr : Q ≤ r*a := min_le_left _ _
  have hQa : Q ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hQC : Q ≤ C := (min_le_right _ _).trans (min_le_right _ _)
  have hrn : Q*(d:ℝ)^2 ≤ r*(n:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hQr (sq_nonneg (d:ℝ))
    have h2 := mul_le_mul_of_nonneg_left hn hr.le
    nlinarith
  have han : Q*(d:ℝ)^2 ≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_right hQa (sq_nonneg (d:ℝ))).trans hn
  have hCd := mul_le_mul_of_nonneg_right hQC (sq_nonneg (d:ℝ))
  have e1 : Real.exp (-r*(n:ℝ)) ≤ Real.exp (-Q*(d:ℝ)^2) :=
    Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (-(n:ℝ)) ≤ Real.exp (-Q*(d:ℝ)^2) :=
    Real.exp_le_exp.mpr (by linarith)
  have e3 : Real.exp (-C*(d:ℝ)^2) ≤ Real.exp (-Q*(d:ℝ)^2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hthree : 3 ≤ Real.exp (Q*(d:ℝ)^2/2) := by
    linarith [Real.add_one_le_exp (Q*(d:ℝ)^2/2)]
  calc
    _ ≤ 3*Real.exp (-Q*(d:ℝ)^2) := by linarith
    _ ≤ Real.exp (Q*(d:ℝ)^2/2)*Real.exp (-Q*(d:ℝ)^2) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms source_constants
#print axioms conjugated_source_margin_lt
#print axioms three_exponentials_absorption
end GaussianEllipsoid.UCFinalScalarAudit
