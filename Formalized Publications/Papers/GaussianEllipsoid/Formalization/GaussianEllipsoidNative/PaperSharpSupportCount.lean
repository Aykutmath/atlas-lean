import FiniteSupportCount
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open scoped BigOperators
namespace GaussianEllipsoid.PaperSharpSupportCount

/-- Exact binomial support entropy; the usual e n/m bound remains valid up to m=n. -/
theorem log_sum_choose_le (n m : ℕ) (hmn : m≤n) :
    Real.log ((∑ k ∈ Finset.range (m+1),n.choose k : ℕ):ℝ) ≤
      (m:ℝ)*Real.log (Real.exp 1*n/m) := by
  by_cases hm : m=0
  · subst m
    simp
  have hmpos : (0:ℝ)<m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hnpos : (0:ℝ)<n := lt_of_lt_of_le hmpos (by exact_mod_cast hmn)
  let t : ℝ := m/n
  let S : ℝ := ∑ k ∈ Finset.range (m+1),(n.choose k:ℝ)
  have ht : 0<t := div_pos hmpos hnpos
  have ht1 : t≤1 := (div_le_one hnpos).mpr (by exact_mod_cast hmn)
  have hS : 0<S := by
    have h : 1≤S := by
      have h0 := Finset.single_le_sum (f := fun k => (n.choose k:ℝ))
        (fun k _ => Nat.cast_nonneg _) (show 0∈Finset.range (m+1) by simp)
      simpa only [Nat.choose_zero_right,Nat.cast_one,S] using h0
    linarith
  have hgen : S*t^m≤(1+t)^n := by
    calc
      _ = ∑ k ∈ Finset.range (m+1),(n.choose k:ℝ)*t^m := by rw [Finset.sum_mul]
      _ ≤ ∑ k ∈ Finset.range (m+1),(n.choose k:ℝ)*t^k := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one ht.le ht1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) (Nat.cast_nonneg _)
      _ ≤ ∑ k ∈ Finset.range (n+1),(n.choose k:ℝ)*t^k := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; positivity)
      _ = (1+t)^n := by
        rw [add_comm (1:ℝ) t,add_pow]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [one_pow,mul_one]
        ring
  have hexp : (1+t)^n≤Real.exp (m:ℝ) := by
    calc
      _ ≤ (Real.exp t)^n := pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) n
      _ = Real.exp ((n:ℝ)*t) := (Real.exp_nat_mul t n).symm
      _ = Real.exp (m:ℝ) := by congr 1; dsimp [t]; field_simp
  have hlogs := Real.log_le_log (mul_pos hS (pow_pos ht _)) (hgen.trans hexp)
  rw [Real.log_mul hS.ne' (pow_ne_zero _ ht.ne'),Real.log_pow,Real.log_exp] at hlogs
  have he : Real.log (Real.exp 1*n/m)=1-Real.log t := by
    dsimp [t]
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hnpos.ne') hmpos.ne',
      Real.log_mul (Real.exp_ne_zero _) hnpos.ne',Real.log_exp,
      Real.log_div hmpos.ne' hnpos.ne']
    ring
  rw [he]
  have hcast : ((∑ k ∈ Finset.range (m+1),n.choose k : ℕ):ℝ)=S := by simp only [Nat.cast_sum,S]
  rw [hcast]
  nlinarith

/-- Exact finite support family count before logarithms. -/
theorem card_supports_le_sum_choose {α : Type*} (u : Finset α) (m : ℕ) :
    ((u.powerset).filter (fun s => s.card≤m)).card≤∑ k ∈ Finset.range (m+1),u.card.choose k := by
  classical
  have hsub : (u.powerset).filter (fun s => s.card≤m) ⊆
      (Finset.range (m+1)).biUnion (fun k => u.powersetCard k) := by
    intro s hs
    obtain ⟨hsu,hsm⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_biUnion.mpr ⟨s.card,Finset.mem_range.mpr (Nat.lt_succ_of_le hsm),
      Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hsu,rfl⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (m+1),(u.powersetCard k).card := Finset.card_biUnion_le
    _ = _ := by simp only [Finset.card_powersetCard]

theorem log_card_supports_le {α : Type*} (u : Finset α) (m : ℕ) (hm : m≤u.card) :
    Real.log (((u.powerset).filter (fun s => s.card≤m)).card:ℝ) ≤
      (m:ℝ)*Real.log (Real.exp 1*u.card/m) := by
  classical
  have hpos : 0<((u.powerset).filter (fun s => s.card≤m)).card :=
    Finset.card_pos.mpr ⟨∅,by simp⟩
  exact (Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast card_supports_le_sum_choose u m)).trans (log_sum_choose_le u.card m hm)

/-- x log(e n/x) is increasing on the source support-budget interval (0,n]. -/
lemma entropy_mono_budget (n a b : ℝ) (ha : 0<a) (hab : a≤b) (hbn : b≤n) :
    a*Real.log (Real.exp 1*n/a) ≤ b*Real.log (Real.exp 1*n/b) := by
  have hb : 0<b := lt_of_lt_of_le ha hab
  have hn : 0<n := lt_of_lt_of_le hb hbn
  have hlognb : 0≤Real.log (n/b) := Real.log_nonneg ((one_le_div hb).mpr hbn)
  have hlogba := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have he (x : ℝ) (hx : 0<x) : Real.log (Real.exp 1*n/x)=1+Real.log n-Real.log x := by
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hn.ne') hx.ne',
      Real.log_mul (Real.exp_ne_zero _) hn.ne',Real.log_exp]
  rw [Real.log_div hb.ne' ha.ne'] at hlogba
  rw [Real.log_div hn.ne' hb.ne'] at hlognb
  have ht := mul_le_mul_of_nonneg_left hlogba ha.le
  have hdiv : a*(b/a)=b := by field_simp
  have hp := mul_le_mul_of_nonneg_right hab hlognb
  simp only [mul_sub, hdiv, mul_one] at ht
  rw [he a ha,he b hb]
  nlinarith

/-- Literal real-valued support budget, including the floor and the exact e n/s logarithm. -/
theorem log_card_supports_floor_le {α : Type*} (u : Finset α) (s : ℝ)
    (hs : 0<s) (hsn : s≤u.card) :
    Real.log (((u.powerset).filter (fun t => (t.card:ℝ)≤s)).card:ℝ) ≤
      s*Real.log (Real.exp 1*u.card/s) := by
  classical
  have hfilter : (u.powerset).filter (fun t => (t.card:ℝ)≤s)=
      (u.powerset).filter (fun t => t.card≤⌊s⌋₊) := by
    ext t
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => (Nat.le_floor_iff hs.le).symm
  rw [hfilter]
  have hfloor : (⌊s⌋₊:ℝ)≤s := Nat.floor_le hs.le
  have hmn : ⌊s⌋₊≤u.card := by exact_mod_cast hfloor.trans hsn
  have hcount := log_card_supports_le u ⌊s⌋₊ hmn
  by_cases hm : ⌊s⌋₊=0
  · rw [hm] at hcount
    simp only [Nat.cast_zero,zero_mul] at hcount
    have hlog : 0≤Real.log (Real.exp 1*u.card/s) := by
      apply Real.log_nonneg
      have he : (1:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
      apply (one_le_div hs).mpr
      nlinarith
    simpa only [hm] using hcount.trans (mul_nonneg hs.le hlog)
  · exact hcount.trans (entropy_mono_budget u.card ⌊s⌋₊ s
      (by exact_mod_cast Nat.pos_of_ne_zero hm) hfloor hsn)

/-- The complementary dense-budget branch is genuinely exponential in the budget,
not the coarser (n+1)^m count. -/
theorem log_card_supports_large_budget {α : Type*} (u : Finset α) (s : ℝ)
    (hs : (u.card:ℝ)/2<s) :
    Real.log (((u.powerset).filter (fun t => (t.card:ℝ)≤s)).card:ℝ) ≤ 2*s*Real.log 2 := by
  classical
  have hs0 : 0<s := lt_of_le_of_lt (by positivity) hs
  have hpos : 0<((u.powerset).filter (fun t => (t.card:ℝ)≤s)).card :=
    Finset.card_pos.mpr ⟨∅,by simp [hs0.le]⟩
  have hc : ((u.powerset).filter (fun t => (t.card:ℝ)≤s)).card≤2^u.card := by
    simpa only [Finset.card_powerset] using Finset.card_le_card (Finset.filter_subset (fun t => (t.card:ℝ)≤s) u.powerset)
  have hlog := Real.log_le_log (show (0:ℝ)<((u.powerset).filter (fun t => (t.card:ℝ)≤s)).card by exact_mod_cast hpos)
    (show (((u.powerset).filter (fun t => (t.card:ℝ)≤s)).card:ℝ)≤(2:ℝ)^u.card by exact_mod_cast hc)
  rw [Real.log_pow] at hlog
  exact hlog.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by norm_num)))

#print axioms log_card_supports_floor_le
#print axioms log_card_supports_large_budget
#print axioms log_card_supports_le
end GaussianEllipsoid.PaperSharpSupportCount
