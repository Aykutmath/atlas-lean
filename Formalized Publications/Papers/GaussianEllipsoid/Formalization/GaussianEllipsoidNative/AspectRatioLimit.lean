import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

open Filter
open scoped ENNReal Topology
namespace GaussianEllipsoidFinalPassage

/-- The strict ENNReal aspect-ratio hypothesis supplies one fixed positive
real gap, even when the ratio has no limit or its limsup is zero. -/
theorem exists_eventual_real_aspect_gap (a : ℕ → ℝ≥0∞)
    (h : limsup a atTop < (1 / 4 : ℝ≥0∞)) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 4 ∧ ∀ᶠ d in atTop, a d < ENNReal.ofReal α := by
  obtain ⟨b, hb1, hb2⟩ := exists_between h
  have hbfin : b ≠ ⊤ := ne_top_of_lt hb2
  have hbpos : 0 < b := (show (0 : ℝ≥0∞) ≤ _ from bot_le).trans_lt hb1
  refine ⟨b.toReal, ENNReal.toReal_pos hbpos.ne' hbfin, ?_, ?_⟩
  · have ht := ENNReal.toReal_lt_toReal hbfin (by norm_num : (1 / 4 : ℝ≥0∞) ≠ ⊤)
    simpa using ht.mpr hb2
  · rw [ENNReal.ofReal_toReal hbfin]
    exact eventually_lt_of_limsup_lt hb1

/-- Explicit natural-number ratio version: no convergence or positive lower
aspect-ratio bound is required. -/
theorem exists_eventual_quadratic_bound (n : ℕ → ℕ)
    (h : limsup (fun d => (n d : ℝ≥0∞) / (d : ℝ≥0∞)^2) atTop <
      (1 / 4 : ℝ≥0∞)) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 4 ∧ ∀ᶠ d in atTop, (n d : ℝ) ≤ α * (d : ℝ)^2 := by
  obtain ⟨α, hα, hαq, he⟩ := exists_eventual_real_aspect_gap _ h
  refine ⟨α, hα, hαq, ?_⟩
  filter_upwards [he, eventually_ge_atTop 1] with d hd hdpos
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hd' : (n d : ℝ) / (d : ℝ)^2 < α := by
    have hnfin : (n d : ℝ≥0∞) / (d : ℝ≥0∞)^2 ≠ ⊤ := ne_top_of_lt hd
    have ht := (ENNReal.toReal_lt_toReal hnfin ENNReal.ofReal_ne_top).mpr hd
    simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hα.le] using ht
  exact (div_lt_iff₀ (sq_pos_of_pos hdR)).mp hd' |>.le

#print axioms exists_eventual_real_aspect_gap
#print axioms exists_eventual_quadratic_bound
end GaussianEllipsoidFinalPassage

