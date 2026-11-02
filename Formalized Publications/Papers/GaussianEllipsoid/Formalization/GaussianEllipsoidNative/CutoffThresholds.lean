import CutoffGeometry

namespace GaussianEllipsoidCandidate
open Finset Filter

/-- A floor loses at most half once its argument is at least two. -/
theorem sparse_floor_lower (x : ℝ) (hx : 2 ≤ x) : x/2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

/-- Every positive multiple of `d / log d` eventually dominates any fixed
threshold. This handles all finite block-size requirements uniformly. -/
theorem eventually_mul_div_log_ge (c B : ℝ) (hc : 0 < c) :
    ∀ᶠ d : ℝ in atTop, B ≤ c*d/Real.log d := by
  let M := max B 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have he := Real.isLittleO_log_id_atTop.bound (div_pos hc hM)
  filter_upwards [he, eventually_gt_atTop (1:ℝ)] with d he hd
  have hd0 : 0 < d := by linarith
  have hl : 0 < Real.log d := Real.log_pos hd
  have he' : Real.log d ≤ (c/M)*d := by
    simpa only [Real.norm_eq_abs, id_eq, abs_of_pos hd0, abs_of_pos hl] using he
  have hm : M * Real.log d ≤ c*d := by
    have := mul_le_mul_of_nonneg_left he' hM.le
    field_simp at this ⊢
    nlinarith
  exact (le_max_left B 1).trans ((le_div_iff₀ hl).2 hm)

/-- The sparse cutoff used by the Gaussian proof is eventually below the
span cutoff, while its floor retains the required half-scale. -/
theorem eventually_sparse_cutoff_bounds :
    ∀ᶠ d : ℝ in atTop,
      0 < Real.log d ∧
      d/(16384*Real.log d) ≤ (⌊d/(8192*Real.log d)⌋₊ : ℝ) ∧
      (⌊d/(8192*Real.log d)⌋₊ : ℝ) ≤ d/256 := by
  have hg := eventually_mul_div_log_ge (1/8192) 2 (by norm_num)
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [hg, hl, eventually_gt_atTop (1:ℝ)] with d hg hl hd
  have hd0 : 0 < d := by linarith
  have hl0 : 0 < Real.log d := by linarith
  have hx : 2 ≤ d/(8192*Real.log d) := by convert hg using 1 <;> ring
  refine ⟨hl0, ?_, ?_⟩
  · convert sparse_floor_lower _ hx using 1 <;> ring
  · have hf := Nat.floor_le (by positivity : 0 ≤ d/(8192*Real.log d))
    have hu : d/(8192*Real.log d) ≤ d/256 := by
      apply (div_le_iff₀ (by positivity : 0 < 8192*Real.log d)).2
      nlinarith
    exact hf.trans hu

/-- Fixed-`T` effective supports exceed the even-block threshold `4096`
eventually. -/
theorem eventually_postprefix_effective_support (T : ℝ) (hT : 0 < T) :
    ∀ᶠ d : ℝ in atTop, 4096 ≤ 3*d/(2097152*T*Real.log d) := by
  have h := eventually_mul_div_log_ge (3/(2097152*T)) 4096 (by positivity)
  filter_upwards [h] with d hd
  convert hd using 1 <;> ring

/-- Cutoffs and all projected/late numerical data for the actual constructor
output. `p` counts sparse-prefix groups and `q` counts captured groups. -/
theorem actual_sparse_span_cutoffs {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (d : ℝ) (hd : 0 < d) (hlog : 0 < Real.log d)
    (hfloor : d/(16384*Real.log d) ≤ (⌊d/(8192*Real.log d)⌋₊ : ℝ))
    (hbudget : (⌊d/(8192*Real.log d)⌋₊ : ℝ) ≤ d/256) :
    ∃ p q : ℕ, p ≤ q ∧
      SupportCutoff (dyadicGroupSize u amp groups T) groups.length
        (⌊d/(8192*Real.log d)⌋₊ : ℝ) p ∧
      SupportCutoff (dyadicGroupSize u amp groups T) groups.length (d/256) q ∧
      (∀ r, p ≤ r → r < groups.length →
        d/(65536*T*Real.log d) ≤ dyadicGroupScale u amp groups r ∧
        3*d/(2097152*T*Real.log d) ≤ dyadicGroupEffectiveSupport u amp groups T r) ∧
      (∀ r, r < q → dyadicGroupEffectiveSupport u amp groups T r ≤ d/4) ∧
      (∀ r, q ≤ r → r < groups.length →
        d/(1024*T) < dyadicGroupScale u amp groups r) := by
  let k := dyadicGroupSize u amp groups T
  let S := dyadicGroupScale u amp groups
  have hk0 : ∀ r, 0 ≤ k r := by intro r; exact Nat.cast_nonneg _
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hS : ∀ r < groups.length, 0 ≤ S r :=
    fun r hr => (actual_group_numerical_bounds u amp groups T hreg r hr).1.le
  have hs := actual_group_doubling u amp groups T hreg hchain
  have hk : ∀ r < groups.length, k r ≤ 2*(T:ℝ)*S r :=
    fun r hr => (actual_group_numerical_bounds u amp groups T hreg r hr).2.2.1
  obtain ⟨p, hp⟩ := exists_supportCutoff k groups.length
    (⌊d/(8192*Real.log d)⌋₊ : ℝ) (by positivity)
  obtain ⟨q, hq⟩ := exists_supportCutoff k groups.length (d/256) (by positivity)
  have hpq := supportCutoff_mono k groups.length _ _ p q hk0 hbudget hp hq
  refine ⟨p, q, hpq, hp, hq, ?_, ?_, ?_⟩
  · intro r hpr hr
    have hlo := record_scale_after_cutoff S k groups.length p T _ hT' hS hs hk hp r hpr hr
    have hbase : d/(65536*T*Real.log d) ≤ S r := by
      have hdiv := div_le_div_of_nonneg_right hfloor (by positivity : 0 ≤ 4*(T:ℝ))
      have heq : d/(16384*Real.log d)/(4*(T:ℝ)) = d/(65536*T*Real.log d) := by ring
      rw [heq] at hdiv
      exact hdiv.trans hlo.le
    refine ⟨hbase, ?_⟩
    have hR := (actual_group_numerical_bounds u amp groups T hreg r hr).2.2.2.1
    have hmul := mul_le_mul_of_nonneg_left hbase (by norm_num : (0:ℝ) ≤ 3/32)
    calc
      3*d/(2097152*T*Real.log d) = (3/32)*(d/(65536*T*Real.log d)) := by ring
      _ ≤ (3/32)*S r := hmul
      _ ≤ _ := hR
  · intro r hrq
    have hr : r < groups.length := lt_of_lt_of_le hrq hq.1
    have hb := actual_group_numerical_bounds u amp groups T hreg r hr
    have hkr : k r ≤ ∑ i ∈ range q, k i :=
      single_le_sum (fun i _ => hk0 i) (mem_range.mpr hrq)
    have hks : k r ≤ d/256 := hkr.trans hq.2.1
    have hSk : S r ≤ k r := hb.2.1
    have hR := hb.2.2.2.2
    dsimp [S, k] at hSk hks
    nlinarith
  · intro r hqr hr
    have hlo := record_scale_after_cutoff S k groups.length q T _ hT' hS hs hk hq r hqr hr
    convert hlo using 1 <;> ring

/-- A residual ambient dimension of `d/3` suffices after removal of the
entire captured support (at most `d/256`). -/
theorem captured_residual_rank_lower (d h removed : ℝ)
    (hd : 0 ≤ d) (hh : d/3 ≤ h) (hrem : removed ≤ d/256) : d/4 ≤ h-removed := by
  linarith

end GaussianEllipsoidCandidate
