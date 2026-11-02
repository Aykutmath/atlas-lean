import RealDyadicPaper
import PaperRhoScalars
import LateGroupCount

noncomputable section
set_option maxHeartbeats 600000
open Finset
namespace GaussianEllipsoidCandidate

/-- A nonempty actual retained group forces the original amplitude positive. -/
lemma real_groups_amplitude_pos {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g∈groups,RealRegularRetainedGroup q u amp T g)
    (hN : 0 < groups.length) : 0 < amp := by
  have hg : groups[0]?.getD [] ∈ groups := by
    simp only [List.getElem?_eq_getElem hN,Option.getD_some]
    exact List.getElem_mem hN
  obtain ⟨t,tail,_,h⟩ := hreg _ hg
  have ha : 0 < amp*(1/2:ℝ)^(t+1) := h.2.1
  exact (mul_pos_iff_of_pos_right (by positivity : 0 < (1/2:ℝ)^(t+1))).mp ha

/-- The paper's exact all-groups logarithmic count. The initial integer base
support is at least1; no additive ambient-n bound or altered logarithm is used. -/
theorem real_actual_group_log_count {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g∈groups,RealRegularRetainedGroup q u amp T g)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (K : ℝ) (d : ℕ) (hsupp : ((univ.filter fun i => u i≠0).card:ℝ) ≤ K*d)
    (hN : 0 < groups.length) :
    1 ≤ K*d ∧ (groups.length:ℝ) ≤ 1+Real.log (K*d)/Real.log q := by
  have hq0 : 0 < q := by linarith
  have ha := real_groups_amplitude_pos q u amp groups T hreg hN
  have hspos := (real_actual_group_numerical_bounds q u amp groups T hreg 0 hN).1
  have hsone : (1:ℝ) ≤ dyadicGroupScale u amp groups 0 := by
    change (1:ℝ) ≤ ((dyadicBin u amp ((groups[0]?.getD []).headD 0)).card:ℝ)
    exact_mod_cast (Nat.succ_le_of_lt (Nat.cast_pos.mp hspos))
  have hupper (r : ℕ) : dyadicGroupScale u amp groups r ≤ K*d :=
    (actual_group_scale_le_support u amp ha groups r).trans hsupp
  have hbase : (1:ℝ) ≤ K*d := hsone.trans (hupper 0)
  refine ⟨hbase,?_⟩
  have hn : 0+(groups.length-1) < groups.length := by omega
  have hg := finite_real_growth_power q hq0.le (dyadicGroupScale u amp groups) groups.length
    (real_actual_group_growth q u amp groups T hreg hchain) 0 (groups.length-1) hn
  have hstep : q^(groups.length-1) ≤
      q^(groups.length-1)*dyadicGroupScale u amp groups 0 := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hsone (pow_nonneg hq0.le (groups.length-1)))
  have hp : q^(groups.length-1) ≤ K*d := hstep.trans (hg.trans (hupper _))
  have hl := Real.log_le_log (pow_pos hq0 _) hp
  rw [Real.log_pow] at hl
  have hdiv := (le_div_iff₀ (Real.log_pos hq)).mpr hl
  have hlen : (groups.length:ℝ)=((groups.length-1:ℕ):ℝ)+1 := by
    exact_mod_cast (Nat.sub_add_cancel (show 1≤groups.length from hN)).symm
  rw [hlen]
  linarith

/-- The empty case is kept separate, so no false logarithmic inequality is
asserted when Kd is too small even though there are no selected groups. -/
theorem real_actual_group_log_count_cases {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g∈groups,RealRegularRetainedGroup q u amp T g)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (K : ℝ) (d : ℕ) (hsupp : ((univ.filter fun i => u i≠0).card:ℝ) ≤ K*d) :
    groups=[] ∨ (1≤K*d ∧ (groups.length:ℝ)≤1+Real.log (K*d)/Real.log q) := by
  by_cases hN : 0 < groups.length
  · exact Or.inr (real_actual_group_log_count q hq u amp groups T hreg hchain K d hsupp hN)
  · exact Or.inl (List.length_eq_zero_iff.mp (by omega))

#print axioms real_actual_group_log_count
#print axioms real_actual_group_log_count_cases
end GaussianEllipsoidCandidate
