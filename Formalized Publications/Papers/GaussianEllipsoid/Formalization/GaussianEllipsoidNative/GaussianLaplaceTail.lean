/- Newly reconstructed analytic support, 2026-10-03. Not recovered original bytes.
   This file does not assume or assert Gaussian concentration. It proves the
   deterministic differential-inequality and Markov steps used by that proof. -/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

noncomputable section
open MeasureTheory Set

namespace GaussianLaplaceTail

/-- Integrating the sharp centered-Laplace differential inequality gives the
exact Gaussian exponential bound. -/
theorem laplace_le_of_derivative_le {M D : ℝ → ℝ}
    (hM : ∀ s, 0 ≤ s → HasDerivAt M (D s) s)
    (hD : ∀ s, 0 ≤ s → D s ≤ s * M s)
    (hzero : M 0 ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    M t ≤ Real.exp (t^2/2) := by
  let F : ℝ → ℝ := fun s => M s * Real.exp (-(s^2/2))
  let F' : ℝ → ℝ := fun s => (D s - s*M s)*Real.exp (-(s^2/2))
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt F (F' s) s := by
    have he := ((((hasDerivAt_id s).pow 2).div_const 2).neg).exp
    exact ((hM s hs).mul he).congr_deriv (by dsimp [F']; ring)
  have ha : AntitoneOn F (Icc 0 t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · exact fun s hs => (hd s hs.1).continuousAt.continuousWithinAt
    · exact fun s hs => (hd s (interior_subset hs).1).hasDerivWithinAt
    · intro s hs
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hD s (interior_subset hs).1))
        (Real.exp_pos _).le
  have hb : M t * Real.exp (-(t^2/2)) ≤ 1 := by
    have := ha ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    simpa only [F, zero_pow (by decide : 2 ≠ 0), zero_div, neg_zero,
      Real.exp_zero, mul_one] using this.trans (by simpa [F] using hzero)
  have hh := mul_le_mul_of_nonneg_right hb (Real.exp_pos (t^2/2)).le
  rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at hh

/-- The strict lower-tail event obeys the sharp Gaussian bound as soon as the
centered negative Laplace transform has its sharp bound at parameter `t`.
The premises here are analytic support obligations, not replacement assumptions
for the paper's missing theorem. -/
theorem strict_lower_tail_of_laplace_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (m t : ℝ)
    (ht : 0 ≤ t)
    (hi : Integrable (fun x => Real.exp (t*(m-f x))) μ)
    (hLaplace : (∫ x, Real.exp (t*(m-f x)) ∂μ) ≤ Real.exp (t^2/2)) :
    μ.real {x | f x < m-t} ≤ Real.exp (-t^2/2) := by
  by_cases hz : t = 0
  · subst t
    simpa only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, probReal_univ]
      using (measureReal_mono (μ := μ) (subset_univ {x | f x < m-0}))
  have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  have hsub : {x | f x < m-t} ⊆ {x | Real.exp (t^2) ≤ Real.exp (t*(m-f x))} := by
    intro x hx
    apply Real.exp_le_exp.mpr
    change f x < m-t at hx
    nlinarith
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun x => (Real.exp_pos (t*(m-f x))).le) hi (Real.exp (t^2))
  have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hsub)
    (Real.exp_pos (t^2)).le
  have hb : Real.exp (t^2) * μ.real {x | f x < m-t} ≤ Real.exp (t^2/2) :=
    hmono.trans (hmark.trans hLaplace)
  have he : Real.exp (t^2) * Real.exp (-t^2/2) = Real.exp (t^2/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he] at hb
  nlinarith [Real.exp_pos (t^2)]

#print axioms laplace_le_of_derivative_le
#print axioms strict_lower_tail_of_laplace_bound
end GaussianLaplaceTail
