import GlobalDyadicRetention
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace GaussianEllipsoidCandidate

open Finset Filter

/-- A cutoff includes exactly a maximal initial segment under a support budget.
The integer counts included groups; subsequent groups are indexed from `p`. -/
def SupportCutoff (k : ℕ → ℝ) (N : ℕ) (budget : ℝ) (p : ℕ) : Prop :=
  p ≤ N ∧ (∑ i ∈ range p, k i) ≤ budget ∧
    ∀ r, p ≤ r → r < N → budget < ∑ i ∈ range (r + 1), k i

/-- Finite nonnegative support budgets have a maximal prefix, including the
empty and all-groups edge cases. -/
theorem exists_supportCutoff (k : ℕ → ℝ) (N : ℕ) (budget : ℝ)
    (hb : 0 ≤ budget) : ∃ p, SupportCutoff k N budget p := by
  induction N with
  | zero => exact ⟨0, le_rfl, by simpa using hb, by omega⟩
  | succ N ih =>
    by_cases h : (∑ i ∈ range (N + 1), k i) ≤ budget
    · exact ⟨N+1, le_rfl, h, by omega⟩
    · obtain ⟨p, hp, hsum, hafter⟩ := ih
      refine ⟨p, by omega, hsum, ?_⟩
      intro r hpr hr
      by_cases hrN : r < N
      · exact hafter r hpr hrN
      · have heq : r = N := by omega
        subst r
        exact lt_of_not_ge h

/-- Larger budgets cannot have an earlier maximal cutoff. -/
theorem supportCutoff_mono (k : ℕ → ℝ) (N : ℕ) (b c : ℝ) (p q : ℕ)
    (hk : ∀ r, 0 ≤ k r) (hbc : b ≤ c)
    (hp : SupportCutoff k N b p) (hq : SupportCutoff k N c q) : p ≤ q := by
  by_contra h
  have hqp : q + 1 ≤ p := by omega
  have hsum : (∑ i ∈ range (q+1), k i) ≤ ∑ i ∈ range p, k i :=
    sum_le_sum_of_subset_of_nonneg (range_mono hqp) (by intro i _ _; exact hk i)
  have hexceed := hq.2.2 q le_rfl (by have := hp.1; omega)
  linarith [hp.2.1]

/-- Doubling is needed only on the finite constructed list. -/
theorem finite_doubling_prefix (S : ℕ → ℝ) (N : ℕ)
    (hS : ∀ r < N, 0 ≤ S r)
    (hstep : ∀ r, r+1 < N → 2 * S r ≤ S (r+1)) :
    ∀ r, r < N → (∑ i ∈ range r, S i) ≤ S r := by
  intro r
  induction r with
  | zero => intro hr; simpa using hS 0 hr
  | succ r ih =>
    intro hr
    rw [sum_range_succ]
    have hi := ih (by omega)
    have hs := hstep r hr
    linarith

/-- The earlier support is at most `2 T S_r`; support through the current
group is at most `4 T S_r`. -/
theorem finite_support_prefix_bounds (S k : ℕ → ℝ) (N : ℕ) (T : ℝ)
    (hT : 0 ≤ T) (hS : ∀ r < N, 0 ≤ S r)
    (hstep : ∀ r, r+1 < N → 2 * S r ≤ S (r+1))
    (hk : ∀ r < N, k r ≤ 2*T*S r) (r : ℕ) (hr : r < N) :
    (∑ i ∈ range r, k i) ≤ 2*T*S r ∧
    (∑ i ∈ range (r+1), k i) ≤ 4*T*S r := by
  have hpre := finite_doubling_prefix S N hS hstep r hr
  have hsum : (∑ i ∈ range r, k i) ≤ 2*T*∑ i ∈ range r, S i := by
    rw [mul_sum]
    exact sum_le_sum (fun i hi => hk i (lt_trans (mem_range.mp hi) hr))
  have hpre' : (∑ i ∈ range r, k i) ≤ 2*T*S r :=
    hsum.trans (mul_le_mul_of_nonneg_left hpre (by positivity))
  refine ⟨hpre', ?_⟩
  rw [sum_range_succ]
  nlinarith [hk r hr]

/-- Every group after a cutoff has macroscopic record support relative to
that cutoff's budget. -/
theorem record_scale_after_cutoff (S k : ℕ → ℝ) (N p : ℕ) (T budget : ℝ)
    (hT : 0 < T) (hS : ∀ r < N, 0 ≤ S r)
    (hstep : ∀ r, r+1 < N → 2 * S r ≤ S (r+1))
    (hk : ∀ r < N, k r ≤ 2*T*S r)
    (hp : SupportCutoff k N budget p) (r : ℕ) (hpr : p ≤ r) (hr : r < N) :
    budget / (4*T) < S r := by
  have hthrough := (finite_support_prefix_bounds S k N T hT.le hS hstep hk r hr).2
  have hexceed := hp.2.2 r hpr hr
  apply (div_lt_iff₀ (by positivity : 0 < 4*T)).2
  nlinarith

/-- Canonical numerical data extracted from the actual dyadic record list. -/
noncomputable def dyadicGroupScale {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (r : ℕ) : ℝ :=
  (dyadicBin u amp ((groups[r]?.getD []).headD 0)).card

noncomputable def dyadicGroupSupport {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T r : ℕ) : Finset ι :=
  recordRetainedSupport u amp ((groups[r]?.getD []).headD 0) (groups[r]?.getD []).tail T

noncomputable def dyadicGroupSize {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T r : ℕ) : ℝ :=
  (dyadicGroupSupport u amp groups T r).card

noncomputable def dyadicGroupEffectiveSupport {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T r : ℕ) : ℝ :=
  (∑ i ∈ dyadicGroupSupport u amp groups T r, |u i|)^2 /
    ∑ i ∈ dyadicGroupSupport u amp groups T r, (u i)^2

/-- The numerical support and effective-support facts are derived from the
constructor's actual retained vectors. -/
theorem actual_group_numerical_bounds {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (r : ℕ) (hr : r < groups.length) :
    0 < dyadicGroupScale u amp groups r ∧
    dyadicGroupScale u amp groups r ≤ dyadicGroupSize u amp groups T r ∧
    dyadicGroupSize u amp groups T r ≤ 2*T*dyadicGroupScale u amp groups r ∧
    (3/32:ℝ)*dyadicGroupScale u amp groups r ≤
      dyadicGroupEffectiveSupport u amp groups T r ∧
    dyadicGroupEffectiveSupport u amp groups T r ≤
      64*dyadicGroupScale u amp groups r := by
  have hg : groups[r]?.getD [] ∈ groups := by
    simp only [List.getElem?_eq_getElem hr, Option.getD_some]
    exact List.getElem_mem hr
  obtain ⟨t, tail, heq, h⟩ := hreg _ hg
  dsimp [dyadicGroupScale, dyadicGroupSize, dyadicGroupSupport,
    dyadicGroupEffectiveSupport]
  rw [heq]
  dsimp only [List.headD_cons, List.tail_cons]
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Successor doubling transfers from the actual greedy record relation to
its canonical numerical sequence. -/
theorem actual_group_doubling {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (r : ℕ) (hr : r+1 < groups.length) :
    2*dyadicGroupScale u amp groups r ≤ dyadicGroupScale u amp groups (r+1) := by
  have hg (i : ℕ) (hi : i < groups.length) : groups[i]?.getD [] ∈ groups := by
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  obtain ⟨t, tail, ht, _⟩ := hreg _ (hg r (by omega))
  obtain ⟨s, rest, hs, _⟩ := hreg _ (hg (r+1) hr)
  have hsucc := (List.isChain_iff_getElem.mp hchain) r (by omega)
  have hsucc' : RecordSuccessor (fun t => (dyadicBin u amp t).card)
      (groups[r]?.getD []) (groups[r+1]?.getD []) := by
    simpa only [List.getElem?_eq_getElem (by omega : r < groups.length),
      List.getElem?_eq_getElem hr, Option.getD_some, List.get_eq_getElem] using hsucc
  rw [ht, hs] at hsucc'
  have hnat : 2 * (dyadicBin u amp t).card ≤ (dyadicBin u amp s).card := by
    simpa [RecordSuccessor] using hsucc'
  dsimp [dyadicGroupScale]
  rw [ht, hs]
  dsimp only [List.headD_cons]
  exact_mod_cast hnat

/-- The actual constructor supplies every hypothesis of the deterministic
prefix estimate, with no abstract decomposition assumption. -/
theorem actual_group_prefix_bounds {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (r : ℕ) (hr : r < groups.length) :
    (∑ i ∈ range r, dyadicGroupSize u amp groups T i) ≤
      2*T*dyadicGroupScale u amp groups r ∧
    (∑ i ∈ range (r+1), dyadicGroupSize u amp groups T i) ≤
      4*T*dyadicGroupScale u amp groups r := by
  exact finite_support_prefix_bounds _ _ groups.length T (by positivity)
    (fun i hi => (actual_group_numerical_bounds u amp groups T hreg i hi).1.le)
    (actual_group_doubling u amp groups T hreg hchain)
    (fun i hi => (actual_group_numerical_bounds u amp groups T hreg i hi).2.2.1) r hr

end GaussianEllipsoidCandidate
