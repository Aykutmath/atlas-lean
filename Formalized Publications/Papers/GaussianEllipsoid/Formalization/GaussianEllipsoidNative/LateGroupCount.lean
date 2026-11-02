import CutoffGeometry

namespace GaussianEllipsoidCandidate
open Finset

/-- Successive doubling gives the exact power-of-two growth from any start. -/
theorem finite_doubling_power (S : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ r, r+1 < N → 2*S r ≤ S (r+1))
    (p n : ℕ) (hpn : p+n < N) : (2:ℝ)^n*S p ≤ S (p+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (by omega)
    have hnext := hstep (p+n) (by omega)
    have hmul := mul_le_mul_of_nonneg_left hprev (by norm_num : (0:ℝ) ≤ 2)
    rw [pow_succ]
    have heq : p+(n+1) = p+n+1 := by omega
    rw [heq]
    nlinarith

/-- This elementary logarithm estimate avoids a numerical approximation. -/
theorem half_le_log_two : (1/2:ℝ) ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)
  rw [Real.log_inv] at h
  norm_num at h ⊢
  linarith

/-- The convenient integer retention width has the required linear bound. -/
theorem retention_width_le (K : ℝ) (hK : 1 ≤ K) :
    ((40+4*⌈K⌉₊ : ℕ) : ℝ) ≤ 48*K := by
  have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ K)
  push_cast
  linarith

/-- The late count is logarithmic, uniformly in `d`.  This theorem uses only
finite doubling, the actual first-late support cutoff, and a support cap. -/
theorem late_group_count_le (S : ℕ → ℝ) (N q : ℕ) (K d T : ℝ)
    (hq : q ≤ N) (hK : 1 ≤ K) (hd : 0 < d) (hT : 0 < T)
    (hTcap : T ≤ 48*K)
    (hstep : ∀ r, r+1 < N → 2*S r ≤ S (r+1))
    (hlate : ∀ r, q ≤ r → r < N → d/(1024*T) < S r)
    (hcap : ∀ r < N, S r ≤ K*d) :
    ((N-q : ℕ) : ℝ) ≤ 17*(1+Real.log K) := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  by_cases heq : q = N
  · subst q
    simp only [Nat.sub_self, Nat.cast_zero]
    positivity
  have hqN : q < N := by omega
  let n := N-q-1
  have hn : q+n < N := by dsimp [n]; omega
  have hpow := finite_doubling_power S N hstep q n hn
  have hbase := hlate q le_rfl hqN
  have hlast := hcap (q+n) hn
  have hp : (0:ℝ) < 2^n := by positivity
  have hprod : (2:ℝ)^n*(d/(1024*T)) < K*d :=
    (mul_lt_mul_of_pos_left hbase hp).trans_le (hpow.trans hlast)
  have hpowcap : (2:ℝ)^n < 1024*T*K := by
    have hx : ((2:ℝ)^n*d) / (1024*T) < K*d := by
      simpa only [mul_div_assoc] using hprod
    have hx' := (div_lt_iff₀ (by positivity : 0 < 1024*T)).mp hx
    nlinarith
  have hpowK : (2:ℝ)^n ≤ 2^16*K^2 := by
    have hmul := mul_le_mul_of_nonneg_left hTcap (by positivity : 0 ≤ 1024*K)
    norm_num at hmul ⊢
    nlinarith [sq_nonneg K]
  have hlogs := Real.log_le_log hp hpowK
  have hKpos : 0 < K := by linarith
  rw [Real.log_pow, Real.log_mul (by norm_num) (pow_ne_zero 2 hKpos.ne'),
    Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs
  have hlog2 := half_le_log_two
  have hcast : ((N-q : ℕ):ℝ) = (n:ℝ)+1 := by
    have : N-q = n+1 := by dsimp [n]; omega
    exact_mod_cast this
  have hnineq : (n:ℝ) ≤ 16+4*Real.log K := by
    by_cases hn16 : (n:ℝ) ≤ 16
    · linarith
    · have hnonneg : 0 ≤ (n:ℝ)-16 := by linarith
      have hm := mul_le_mul_of_nonneg_left hlog2 hnonneg
      nlinarith
  rw [hcast]
  linarith

/-- Every base bin is a subset of the coefficient support. -/
theorem actual_group_scale_le_support {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (groups : List (List ℕ)) (r : ℕ) :
    dyadicGroupScale u amp groups r ≤
      ((Finset.univ.filter fun i => u i ≠ 0).card : ℝ) := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i, ?_⟩
  have hb := (mem_dyadicBin u amp _ i).mp hi
  have hl : 0 < amp*(1/2:ℝ)^((groups[r]?.getD []).headD 0 + 1) := by positivity
  intro hz
  have hb0 := hb.1
  rw [hz, abs_zero] at hb0
  exact (not_lt_of_ge (by positivity)) hb0

/-- Consumer-facing count for the same concrete list and sparse support
constraint supplied to the final mixed-norm argument. -/
theorem actual_late_group_count_le {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (groups : List (List ℕ))
    (K d : ℝ) (hK : 1 ≤ K) (hd : 0 < d)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card : ℝ) ≤ K*d)
    (T : ℕ) (hT : T = 40+4*⌈K⌉₊)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (q : ℕ) (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length (d/256) q) :
    ((groups.length-q : ℕ) : ℝ) ≤ 17*(1+Real.log K) := by
  classical
  have hTpos : (0:ℝ) < T := by rw [hT]; positivity
  refine late_group_count_le (dyadicGroupScale u amp groups) groups.length q K d T
    hq.1 hK hd hTpos ?_ (actual_group_doubling u amp groups T hreg hchain) ?_ ?_
  · rw [hT]
    exact retention_width_le K hK
  · intro r hqr hr
    have hh := record_scale_after_cutoff (dyadicGroupScale u amp groups)
      (dyadicGroupSize u amp groups T) groups.length q T (d/256) hTpos
      (fun i hi => (actual_group_numerical_bounds u amp groups T hreg i hi).1.le)
      (actual_group_doubling u amp groups T hreg hchain)
      (fun i hi => (actual_group_numerical_bounds u amp groups T hreg i hi).2.2.1)
      hq r hqr hr
    convert hh using 1 <;> ring
  · intro r hr
    exact (actual_group_scale_le_support u amp ha groups r).trans hsupp

end GaussianEllipsoidCandidate
