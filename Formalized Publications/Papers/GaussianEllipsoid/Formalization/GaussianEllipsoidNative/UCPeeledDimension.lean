import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace UCEscape

/-- Uniform dimension control for every head rank j≤K once d≥2K. -/
theorem peeled_dimension_bounds (d K j : ℕ) (hd : 0 < d) (hK : 2*K ≤ d) (hj : j ≤ K) :
    0 < d-j ∧ ((d:ℝ)/2 ≤ (d-j:ℕ)) ∧ ((d-j:ℕ):ℝ) ≤ d := by
  have hp : 0 < d-j := by omega
  have hhalf : d ≤ 2*(d-j) := by omega
  have hhalfR : (d:ℝ) ≤ 2*((d-j:ℕ):ℝ) := by exact_mod_cast hhalf
  exact ⟨hp, by linarith, by exact_mod_cast Nat.sub_le d j⟩

/-- A fixed expanded upper aspect bound works for all head ranks, so the
analytic constants can be chosen before the spectral peeling budget. -/
theorem peeled_aspect_bounds (n d K j : ℕ) (αm αp : ℝ)
    (hd : 0 < d) (hK : 2*K ≤ d) (hj : j ≤ K)
    (hαm : 0 ≤ αm) (hαp : 0 ≤ αp)
    (hnlo : αm*(d:ℝ)^2 ≤ n) (hnhi : (n:ℝ) ≤ αp*(d:ℝ)^2) :
    αm*((d-j:ℕ):ℝ)^2 ≤ n ∧ (n:ℝ) ≤ (4*αp)*((d-j:ℕ):ℝ)^2 := by
  obtain ⟨_,hh,hle⟩ := peeled_dimension_bounds d K j hd hK hj
  have hp0 : (0:ℝ) ≤ (d-j:ℕ) := Nat.cast_nonneg _
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hsq1 : ((d-j:ℕ):ℝ)^2 ≤ (d:ℝ)^2 := by nlinarith
  have hsq2 : (d:ℝ)^2 ≤ 4*((d-j:ℕ):ℝ)^2 := by nlinarith
  constructor
  · exact (mul_le_mul_of_nonneg_left hsq1 hαm).trans hnlo
  · have h := mul_le_mul_of_nonneg_left hsq2 hαp
    nlinarith

theorem peeled_exponential_bound (d K j : ℕ) (C : ℝ)
    (hd : 0 < d) (hK : 2*K ≤ d) (hj : j ≤ K) (hC : 0 ≤ C) :
    Real.exp (-C*((d-j:ℕ):ℝ)^2) ≤ Real.exp (-(C/4)*(d:ℝ)^2) := by
  obtain ⟨_,hh,_⟩ := peeled_dimension_bounds d K j hd hK hj
  have hp0 : (0:ℝ) ≤ (d-j:ℕ) := Nat.cast_nonneg _
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hsq : (d:ℝ)^2 ≤ 4*((d-j:ℕ):ℝ)^2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hsq hC
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms peeled_aspect_bounds
#print axioms peeled_exponential_bound
end UCEscape
