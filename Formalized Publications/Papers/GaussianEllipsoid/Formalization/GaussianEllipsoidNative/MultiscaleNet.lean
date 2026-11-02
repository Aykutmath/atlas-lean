import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace GaussianEllipsoidCandidate

open Finset

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def coefficientMass (u : ι → ℝ) : ℝ := ∑ i, |u i|
noncomputable def synthesis (A : ι → E) (u : ι → ℝ) : E := ∑ i, u i • A i

lemma coefficientMass_nonneg (u : ι → ℝ) : 0 ≤ coefficientMass u :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma coefficientMass_smul (t : ℝ) (u : ι → ℝ) :
    coefficientMass (t • u) = |t| * coefficientMass u := by
  simp [coefficientMass, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

lemma synthesis_smul (A : ι → E) (t : ℝ) (u : ι → ℝ) :
    synthesis A (t • u) = t • synthesis A u := by
  simp [synthesis, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma synthesis_sub (A : ι → E) (u v : ι → ℝ) :
    synthesis A (u - v) = synthesis A u - synthesis A v := by
  simp [synthesis, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- The global atom event implies the required uniform l1 continuity. -/
theorem synthesis_norm_le (A : ι → E) (C : ℝ) (hA : ∀ i, ‖A i‖ ≤ C)
    (u : ι → ℝ) : ‖synthesis A u‖ ≤ C * coefficientMass u := by
  calc
    ‖synthesis A u‖ ≤ ∑ i, ‖u i • A i‖ := norm_sum_le _ _
    _ = ∑ i, |u i| * ‖A i‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |u i| * C := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hA i) (abs_nonneg _)
    _ = C * coefficientMass u := by
      simp only [coefficientMass, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Uniform sphere bound extends from a deterministic l1 net. The coefficient
net may be any finite set; its existence/cardinality are separate obligations. -/
theorem synthesis_lower_of_net (A : ι → E) (C c δ : ℝ)
    (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (N : Finset (ι → ℝ)) (u : ι → ℝ)
    (hnet : ∃ v ∈ N, coefficientMass (u - v) ≤ δ)
    (hlower : ∀ v ∈ N, c ≤ ‖synthesis A v‖) :
    c - C * δ ≤ ‖synthesis A u‖ := by
  obtain ⟨v, hv, hdist⟩ := hnet
  have herror : ‖synthesis A u - synthesis A v‖ ≤ C * δ := by
    rw [← synthesis_sub]
    exact (synthesis_norm_le A C hA (u - v)).trans (mul_le_mul_of_nonneg_left hdist hC)
  have ht := norm_sub_le (synthesis A u) (synthesis A u - synthesis A v)
  have hid : synthesis A u - (synthesis A u - synthesis A v) = synthesis A v := by abel
  rw [hid] at ht
  have hvbound := hlower v hv
  linarith

/-- Homogeneity extends a sparse l1-sphere lower bound to every coefficient
vector on the same support, without any positivity assumption on c. -/
theorem synthesis_lower_of_unit_mass (A : ι → E) (I : Finset ι) (c : ℝ)
    (hunit : ∀ v : ι → ℝ, (∀ i, i ∉ I → v i = 0) →
      coefficientMass v = 1 → c ≤ ‖synthesis A v‖)
    (u : ι → ℝ) (hsupp : ∀ i, i ∉ I → u i = 0) :
    c * coefficientMass u ≤ ‖synthesis A u‖ := by
  by_cases hz : coefficientMass u = 0
  · simp [hz]
  · have hr : 0 < coefficientMass u :=
      lt_of_le_of_ne (coefficientMass_nonneg u) (Ne.symm hz)
    let v : ι → ℝ := (coefficientMass u)⁻¹ • u
    have hv_support : ∀ i, i ∉ I → v i = 0 := by
      intro i hi
      simp [v, hsupp i hi]
    have hv_mass : coefficientMass v = 1 := by
      rw [show v = (coefficientMass u)⁻¹ • u from rfl, coefficientMass_smul]
      rw [abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hz]
    have hv := hunit v hv_support hv_mass
    rw [show v = (coefficientMass u)⁻¹ • u from rfl, synthesis_smul, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_eq_div] at hv
    exact (le_div_iff₀ hr).1 hv

#print axioms synthesis_norm_le
#print axioms synthesis_lower_of_net
#print axioms synthesis_lower_of_unit_mass

end GaussianEllipsoidCandidate
