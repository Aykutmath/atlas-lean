import AspectRatioLimit
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

open Filter
open scoped Topology ENNReal
namespace GaussianEllipsoidFinalPassage

/-- Ceil rounding has no effect on a positive quadratic asymptotic ratio. -/
theorem tendsto_ceil_quadratic_ratio (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun d : ℕ => (⌈a*(d:ℝ)^2⌉₊ : ℝ)/(d:ℝ)^2) atTop (𝓝 a) := by
  have hi : Tendsto (fun d : ℕ => (d:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun d : ℕ => a+((d:ℝ)⁻¹)^2) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add (hi.pow 2)
  apply tendsto_const_nhds.squeeze' hup
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have hdR : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
    apply (le_div_iff₀ (sq_pos_of_pos hdR)).2
    exact Nat.le_ceil _
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have hdR : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
    apply (div_le_iff₀ (sq_pos_of_pos hdR)).2
    have hc := Nat.ceil_lt_add_one (mul_nonneg ha (sq_nonneg (d:ℝ)))
    have he : (a+((d:ℝ)⁻¹)^2)*(d:ℝ)^2 = a*(d:ℝ)^2+1 := by
      field_simp
    rw [he]
    exact hc.le

/-- Padding permits the final exact-fitting theorem to reduce arbitrary strict
limsup sequences (including zero or oscillating aspect) to a sequence with a
fixed positive limiting aspect. No such lower-aspect assumption is added to
the original sequence. -/
theorem exists_dominating_positive_aspect_sequence (n : ℕ → ℕ)
    (haspect : limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞)) :
    ∃ a : ℝ, 0 < a ∧ a < 1/4 ∧ ∃ N : ℕ → ℕ,
      (∀ d, n d ≤ N d) ∧
      Tendsto (fun d => (N d:ℝ)/(d:ℝ)^2) atTop (𝓝 a) ∧
      (∀ d : ℕ, a*(d:ℝ)^2 ≤ (N d:ℝ)) := by
  obtain ⟨a,ha,haq,hn⟩ := exists_eventual_quadratic_bound n haspect
  let N (d : ℕ) := max (n d) ⌈a*(d:ℝ)^2⌉₊
  refine ⟨a,ha,haq,N,(fun d => le_max_left _ _),?_,?_⟩
  · have he : (fun d : ℕ => (⌈a*(d:ℝ)^2⌉₊:ℝ)/(d:ℝ)^2) =ᶠ[atTop]
        (fun d => (N d:ℝ)/(d:ℝ)^2) := by
      filter_upwards [hn] with d hd
      have hceil : n d ≤ ⌈a*(d:ℝ)^2⌉₊ := by
        exact_mod_cast hd.trans (Nat.le_ceil _)
      simp [N, max_eq_right hceil]
    exact (tendsto_ceil_quadratic_ratio a ha.le).congr' he
  · intro d
    have hc : a*(d:ℝ)^2 ≤ (⌈a*(d:ℝ)^2⌉₊:ℝ) := Nat.le_ceil _
    have hm : ⌈a*(d:ℝ)^2⌉₊ ≤ N d := le_max_right _ _
    exact hc.trans (Nat.cast_le.mpr hm)

/-- Real ratio convergence transfers to the exact ENNReal ratio used by the
project interface; the exceptional zero dimension is explicitly discarded. -/
theorem tendsto_ennreal_quadratic_ratio (n : ℕ → ℕ) (a : ℝ)
    (h : Tendsto (fun d => (n d:ℝ)/(d:ℝ)^2) atTop (𝓝 a)) :
    Tendsto (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop (𝓝 (ENNReal.ofReal a)) := by
  have he : (fun d : ℕ => ENNReal.ofReal ((n d:ℝ)/(d:ℝ)^2)) =ᶠ[atTop]
      (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) := by
    filter_upwards [eventually_ge_atTop 1] with d hd
    have hp : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
    rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos hp), ENNReal.ofReal_pow hp.le]
    simp
  exact (ENNReal.tendsto_ofReal h).congr' he

/-- Strongly quantified padding endpoint for the eventual exact-fitting
assembly: domination, positive limiting aspect and the same strict threshold. -/
theorem exists_dominating_subcritical_sequence (n : ℕ → ℕ)
    (hpos : ∀ d, 0 < n d)
    (haspect : limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞)) :
    ∃ a : ℝ, 0 < a ∧ a < 1/4 ∧ ∃ N : ℕ → ℕ,
      (∀ d, n d ≤ N d) ∧ (∀ d, 0 < N d) ∧
      Tendsto (fun d => (N d:ℝ)/(d:ℝ)^2) atTop (𝓝 a) ∧
      limsup (fun d => (N d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞) ∧
      (∀ d : ℕ, a*(d:ℝ)^2 ≤ (N d:ℝ)) := by
  obtain ⟨a,ha,haq,N,hdom,hlim,hlower⟩ := exists_dominating_positive_aspect_sequence n haspect
  refine ⟨a,ha,haq,N,hdom,(fun d => (hpos d).trans_le (hdom d)),hlim,?_,hlower⟩
  rw [(tendsto_ennreal_quadratic_ratio N a hlim).limsup_eq]
  have hquarter : ENNReal.ofReal (1/4:ℝ) = (1/4:ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
    norm_num
  rw [← hquarter]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1/4)).2 haq

/-- An eventual quadratic sample bound extends to every positive dimension
by enlarging only a fixed constant. This matches finite-dimensional analytic
interfaces without imposing any finite-prefix restriction on the sequence. -/
theorem exists_global_quadratic_upper_bound (n : ℕ → ℕ) (C : ℝ)
    (h : ∀ᶠ d in atTop, (n d:ℝ) ≤ C*(d:ℝ)^2) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℕ, 0 < d → (n d:ℝ) ≤ A*(d:ℝ)^2 := by
  obtain ⟨D,hD⟩ := eventually_atTop.1 h
  let S : ℝ := ∑ i ∈ Finset.range D, (n i:ℝ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let A : ℝ := max 1 C + S
  have hA : 1 ≤ A := by dsimp [A]; linarith [le_max_left (1:ℝ) C]
  have hCA : C ≤ A := by dsimp [A]; linarith [le_max_right (1:ℝ) C]
  refine ⟨A,hA,?_⟩
  intro d hd
  by_cases hDd : D ≤ d
  · exact (hD d hDd).trans (mul_le_mul_of_nonneg_right hCA (sq_nonneg _))
  · have hdD : d < D := by omega
    have hnd : (n d:ℝ) ≤ S := by
      apply Finset.single_le_sum (fun i _ => Nat.cast_nonneg (n i))
      exact Finset.mem_range.mpr hdD
    have hSA : S ≤ A := by dsimp [A]; linarith [le_max_left (1:ℝ) C]
    have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hsq : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith
    exact (hnd.trans hSA).trans (by nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ A)])

#print axioms exists_global_quadratic_upper_bound
#print axioms tendsto_ennreal_quadratic_ratio
#print axioms exists_dominating_subcritical_sequence
#print axioms tendsto_ceil_quadratic_ratio
#print axioms exists_dominating_positive_aspect_sequence
end GaussianEllipsoidFinalPassage
