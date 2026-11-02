import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import FiniteSupportCount

open scoped BigOperators
namespace GaussianEllipsoid
set_option maxHeartbeats 1200000

noncomputable def entropyGap (α : ℝ) : ℝ := 1 / 4 - α
noncomputable def entropyC0 (α B β L : ℝ) : ℝ :=
  (1 / 4) * Real.log (max 1 (1280 / β)) + α * Real.log (1 + 8 * B * L)
noncomputable def entropyEll (α B β L : ℝ) : ℝ :=
  2 * (entropyC0 α B β L + 2) / entropyGap α
noncomputable def entropyScale (α B β L : ℝ) : ℝ :=
  Real.exp (-entropyEll α B β L)
noncomputable def entropyC1 (α A B β L : ℝ) : ℝ :=
  Real.log (α + 1) + Real.log (1 + 8 * A * L / entropyScale α B β L)
noncomputable def entropyCutoff (α A B β K L : ℝ) : ℕ :=
  ⌈max 12 (max (3 / entropyGap α)
    (max (2 * K * entropyC1 α A B β L) (100 * K ^ 2)))⌉₊

lemma entropy_constants {α A B β L : ℝ}
    (hα : 0 < α) (hα' : α < 1 / 4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hL : 0 < L) :
    0 < entropyGap α ∧ 0 ≤ entropyC0 α B β L ∧ 0 < entropyEll α B β L ∧
    0 < entropyScale α B β L ∧ entropyScale α B β L ≤ 1 ∧
    0 ≤ entropyC1 α A B β L := by
  have hg : 0 < entropyGap α := by unfold entropyGap; linarith
  have hq : 0 ≤ Real.log (max 1 (1280 / β)) :=
    Real.log_nonneg (le_max_left _ _)
  have ht : 0 ≤ Real.log (1 + 8 * B * L) := Real.log_nonneg (by exact le_add_of_nonneg_right (by positivity))
  have hC0 : 0 ≤ entropyC0 α B β L := by unfold entropyC0; positivity
  have hell : 0 < entropyEll α B β L := by unfold entropyEll; positivity
  have hc : 0 < entropyScale α B β L := Real.exp_pos _
  have hc1 : entropyScale α B β L ≤ 1 := by
    unfold entropyScale
    exact Real.exp_le_one_iff.mpr (le_of_lt (neg_neg_of_pos hell))
  refine ⟨hg, hC0, hell, hc, hc1, ?_⟩
  unfold entropyC1
  exact add_nonneg (Real.log_nonneg (by linarith))
    (Real.log_nonneg (by exact le_add_of_nonneg_right (by positivity)))

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt (le_of_lt hx)] at h
  linarith

lemma entropy_dimension_bounds (d n : ℕ) {α : ℝ}
    (hd : (12 : ℝ) ≤ d) (hα : α < 1 / 4)
    (hcut : 3 / entropyGap α ≤ d) (hn : (n : ℝ) ≤ α * (d : ℝ)^2) :
    (((2 * (d / 4))^2 : ℕ) : ℝ) ≤ (d : ℝ)^2 / 4 ∧
    (entropyGap α / 2) * (d : ℝ)^2 ≤ (((2 * (d / 4))^2 : ℕ) : ℝ) - n := by
  have hg : 0 < entropyGap α := by unfold entropyGap; linarith
  have hrem : d % 4 ≤ 3 := by omega
  have hdiv := Nat.mod_add_div d 4
  have hrem0 : (0:ℝ) ≤ ((d % 4 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrem3 : ((d % 4 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hrem
  have heq : ((d % 4 : ℕ) : ℝ) + 4 * (d / 4 : ℕ) = (d : ℝ) := by exact_mod_cast hdiv
  have hh0 : (0:ℝ) ≤ (2 * (d / 4) : ℕ) := Nat.cast_nonneg _
  have hhlow : ((d : ℝ) - 3) / 2 ≤ (2 * (d / 4) : ℕ) := by
    push_cast
    linarith
  have hhup : ((2 * (d / 4) : ℕ) : ℝ) ≤ (d : ℝ) / 2 := by
    push_cast
    linarith
  have hsqlo : (d : ℝ)^2 / 4 - 3 * d / 2 ≤ (((2 * (d / 4))^2 : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    nlinarith
  have hgd : 3 ≤ entropyGap α * d := (div_le_iff₀ hg).mp hcut |>.trans_eq (mul_comm _ _)
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg _
  constructor
  · rw [Nat.cast_pow]
    nlinarith
  · unfold entropyGap at *
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hgd)]

lemma entropy_log_base {α B β L : ℝ} (hα : 0 < α) (hα' : α < 1/4)
    (hB : 0 < B) (hβ : 0 < β) (hL : 0 < L) :
    Real.log (1280 * entropyScale α B β L / β) ≤
      Real.log (max 1 (1280 / β)) - entropyEll α B β L ∧
    Real.log (1 + 8 * B * L / entropyScale α B β L) ≤
      Real.log (1 + 8 * B * L) + entropyEll α B β L := by
  obtain ⟨hg, hC0, hell, hc, hc1, hC1⟩ := entropy_constants hα hα' (show (0:ℝ)<1 by norm_num) hB hβ hL
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hc0 : entropyScale α B β L ≠ 0 := ne_of_gt hc
  have hlogc : Real.log (entropyScale α B β L) = -entropyEll α B β L := by
    unfold entropyScale; rw [Real.log_exp]
  constructor
  · have hpos : 0 < 1280 / β := by positivity
    have heq : 1280 * entropyScale α B β L / β = (1280 / β) * entropyScale α B β L := by ring
    rw [heq, Real.log_mul (ne_of_gt hpos) hc0, hlogc]
    have hlog := Real.log_le_log hpos (le_max_right 1 (1280/β))
    linarith
  · have hbound : 1 + 8 * B * L / entropyScale α B β L ≤
        (1 + 8 * B * L) / entropyScale α B β L := by
      apply (le_div_iff₀ hc).mpr
      field_simp
      nlinarith
    have ht : 0 < 1 + 8 * B * L := by positivity
    have h := Real.log_le_log (show 0 < 1 + 8 * B * L / entropyScale α B β L by positivity) hbound
    rw [Real.log_div (ne_of_gt ht) hc0, hlogc] at h
    linarith

lemma entropy_log_head {α A c L : ℝ} {d n : ℕ}
    (hα : 0 < α) (hA : 0 < A) (hc : 0 < c) (hL : 0 < L)
    (hd : (1 : ℝ) ≤ d) (hn : (n : ℝ) ≤ α * (d : ℝ)^2) :
    Real.log ((n : ℝ) + 1) + Real.log (1 + 8 * A * L * Real.sqrt d / c) ≤
      Real.log (α+1) + Real.log (1 + 8*A*L/c) + (5/2)*Real.log d := by
  have hd0 : (0:ℝ) < d := lt_of_lt_of_le zero_lt_one hd
  have hs : (1:ℝ) ≤ Real.sqrt d := by simpa using Real.sqrt_le_sqrt hd
  have hα1 : 0 < α+1 := by linarith
  have hn1 : (n : ℝ)+1 ≤ (α+1)*(d:ℝ)^2 := by nlinarith [sq_nonneg ((d:ℝ)-1)]
  have hln := Real.log_le_log (show 0 < (n:ℝ)+1 by positivity) hn1
  rw [Real.log_mul (ne_of_gt hα1) (ne_of_gt (sq_pos_of_pos hd0)), Real.log_pow] at hln
  have hbase : 0 < 1+8*A*L/c := by positivity
  have hh : 1+8*A*L*Real.sqrt d/c ≤ (1+8*A*L/c)*Real.sqrt d := by
    calc
      _ = 1 + (8*A*L/c)*Real.sqrt d := by ring
      _ ≤ Real.sqrt d + (8*A*L/c)*Real.sqrt d := add_le_add_left hs _
      _ = _ := by ring
  have hlh := Real.log_le_log (show 0 < 1+8*A*L*Real.sqrt d/c by positivity) hh
  rw [Real.log_mul (ne_of_gt hbase) (ne_of_gt (lt_of_lt_of_le zero_lt_one hs)),
    Real.log_sqrt (le_of_lt hd0)] at hlh
  norm_num at hln
  linarith only [hln, hlh]

lemma entropy_head_exponent {α A B β K L : ℝ} {d n m : ℕ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K) (hL : 0 < L)
    (hd : (1 : ℝ) ≤ d) (hn : (n : ℝ) ≤ α*(d:ℝ)^2)
    (hm : (m:ℝ) ≤ K*d) (hcut₁ : 2*K*entropyC1 α A B β L ≤ d)
    (hcut₂ : 100*K^2 ≤ d) :
    (m:ℝ) * (Real.log ((n:ℝ)+1) +
      Real.log (1+8*A*L*Real.sqrt d / entropyScale α B β L)) ≤ (d:ℝ)^2 := by
  obtain ⟨hg, hC0, hell, hc, hc1, hC1⟩ := entropy_constants hα hα' hA hB hβ hL
  have hd0 : (0:ℝ) < d := lt_of_lt_of_le zero_lt_one hd
  have hlog := entropy_log_head hα hA hc hL hd hn
  change _ ≤ entropyC1 α A B β L + (5/2)*Real.log d at hlog
  have hlogs0 : 0 ≤ Real.log ((n:ℝ)+1) +
      Real.log (1+8*A*L*Real.sqrt d / entropyScale α B β L) :=
    add_nonneg (Real.log_nonneg (by exact le_add_of_nonneg_left (Nat.cast_nonneg n)))
      (Real.log_nonneg (by exact le_add_of_nonneg_right (by positivity)))
  have h₁ := mul_le_mul_of_nonneg_left hlog (show 0 ≤ K*(d:ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hm hlogs0
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsq : (Real.sqrt d)^2 = (d:ℝ) := Real.sq_sqrt (le_of_lt hd0)
  have hsK : 10*K ≤ Real.sqrt d := by nlinarith only [hcut₂, hsq, hs0, hK]
  have hlogd := log_le_two_sqrt hd0
  have hterm₁ : K*(d:ℝ)*entropyC1 α A B β L ≤ (d:ℝ)^2/2 := by
    nlinarith only [mul_nonneg (le_of_lt hd0) (sub_nonneg.mpr hcut₁)]
  have hterm₂ : K*(d:ℝ)*((5/2)*Real.log d) ≤ (d:ℝ)^2/2 := by
    have hlogmul := mul_le_mul_of_nonneg_left hlogd (show 0 ≤ (5/2)*K*(d:ℝ) by positivity)
    have hKs : 10*K*Real.sqrt d ≤ (d:ℝ) := by
      nlinarith only [hsq, mul_nonneg hs0 (sub_nonneg.mpr hsK)]
    nlinarith only [hlogmul, mul_nonneg (le_of_lt hd0) (sub_nonneg.mpr hKs)]
  calc
    _ ≤ K*(d:ℝ)*(entropyC1 α A B β L+(5/2)*Real.log d) := h₂.trans h₁
    _ ≤ _ := by nlinarith only [hterm₁, hterm₂]

lemma entropy_base_exponent {α A B β L : ℝ} {d n h : ℕ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hL : 0 < L)
    (hn : (n:ℝ) ≤ α*(d:ℝ)^2)
    (hup : ((h^2:ℕ):ℝ) ≤ (d:ℝ)^2/4)
    (hgap : (entropyGap α/2)*(d:ℝ)^2 ≤ ((h^2:ℕ):ℝ)-(n:ℝ)) :
    ((h^2:ℕ):ℝ)*Real.log (1280*entropyScale α B β L/β) +
      (n:ℝ)*Real.log (1+8*B*L/entropyScale α B β L) ≤ -2*(d:ℝ)^2 := by
  obtain ⟨hg, hC0, hell, hc, hc1, hC1⟩ := entropy_constants hα hα' hA hB hβ hL
  obtain ⟨hb, ht⟩ := entropy_log_base hα hα' hB hβ hL
  have hq0 : 0 ≤ Real.log (max 1 (1280/β)) := Real.log_nonneg (le_max_left _ _)
  have ht0 : 0 ≤ Real.log (1+8*B*L) := Real.log_nonneg (by exact le_add_of_nonneg_right (by positivity))
  have heq : (entropyGap α / 2) * entropyEll α B β L = entropyC0 α B β L + 2 := by
    unfold entropyEll
    field_simp <;> ring
  have h₁ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (h^2))
  have h₂ := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
  have h₃ := mul_le_mul_of_nonneg_right hup hq0
  have h₄ := mul_le_mul_of_nonneg_right hn ht0
  have h₅ := mul_le_mul_of_nonneg_right hgap (le_of_lt hell)
  have hcoeff : ((h^2:ℕ):ℝ)*Real.log (max 1 (1280/β)) +
      (n:ℝ)*Real.log (1+8*B*L) ≤ entropyC0 α B β L*(d:ℝ)^2 := by
    unfold entropyC0
    nlinarith only [h₃, h₄]
  have hneg : -(((h^2:ℕ):ℝ)-(n:ℝ))*entropyEll α B β L ≤
      -(entropyC0 α B β L+2)*(d:ℝ)^2 := by
    calc
      _ ≤ -((entropyGap α/2)*(d:ℝ)^2)*entropyEll α B β L := by linarith only [h₅]
      _ = _ := by nlinarith only [congrArg (fun x : ℝ => x * (d:ℝ)^2) heq]
  nlinarith only [h₁, h₂, hcoeff, hneg]

/-- Explicit scalar entropy estimate. The support exponent may be any natural number
bounded by Kd; it need not be exactly the maximum support size. -/
theorem localized_entropy_product_le {α A B β K L : ℝ} {d n m : ℕ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K) (hL : 0 < L)
    (hd : entropyCutoff α A B β K L ≤ d)
    (hn : (n:ℝ) ≤ α*(d:ℝ)^2) (hm : (m:ℝ) ≤ K*d) :
    (1280*entropyScale α B β L/β)^((2*(d/4))^2) *
      ((n:ℝ)+1)^m *
      (1+8*A*L*Real.sqrt d/entropyScale α B β L)^m *
      (1+8*B*L/entropyScale α B β L)^n ≤ Real.exp (-(d:ℝ)^2) := by
  obtain ⟨hg, hC0, hell, hc, hc1, hC1⟩ := entropy_constants hα hα' hA hB hβ hL
  have hcut : max 12 (max (3/entropyGap α)
      (max (2*K*entropyC1 α A B β L) (100*K^2))) ≤ (d:ℝ) := by
    have hcast : (entropyCutoff α A B β K L : ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    exact (Nat.le_ceil _).trans hcast
  have hd12 : (12:ℝ) ≤ d := (le_max_left _ _).trans hcut
  have hcutg : 3/entropyGap α ≤ d :=
    (le_max_of_le_right (le_max_left _ _)).trans hcut
  have hcut1 : 2*K*entropyC1 α A B β L ≤ d :=
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hcut
  have hcut2 : 100*K^2 ≤ d :=
    (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))).trans hcut
  obtain ⟨hup, hgap⟩ := entropy_dimension_bounds d n hd12 hα' hcutg hn
  have hbase := entropy_base_exponent hα hα' hA hB hβ hL hn hup hgap
  have hhead := entropy_head_exponent hα hα' hA hB hβ hK hL
    (show (1:ℝ) ≤ d by linarith only [hd12]) hn hm hcut1 hcut2
  have hr : 0 < 1280*entropyScale α B β L/β := by positivity
  have hnp : 0 < (n:ℝ)+1 := by positivity
  have hhp : 0 < 1+8*A*L*Real.sqrt d/entropyScale α B β L := by positivity
  have htp : 0 < 1+8*B*L/entropyScale α B β L := by positivity
  calc
    _ = Real.exp (
        (((2*(d/4))^2:ℕ):ℝ)*Real.log (1280*entropyScale α B β L/β) +
        (m:ℝ)*(Real.log ((n:ℝ)+1)+Real.log (1+8*A*L*Real.sqrt d/entropyScale α B β L)) +
        (n:ℝ)*Real.log (1+8*B*L/entropyScale α B β L)) := by
      rw [mul_add]
      simp only [Real.exp_add, Real.exp_nat_mul, Real.exp_log hr, Real.exp_log hnp,
        Real.exp_log hhp, Real.exp_log htp]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hbase, hhead])

/-- The exact min/floor exponent used by the localized two-net probability proof. -/
theorem localized_entropy_min_floor_le {α A B β K L : ℝ} {d n : ℕ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K) (hL : 0 < L)
    (hd : entropyCutoff α A B β K L ≤ d)
    (hn : (n:ℝ) ≤ α*(d:ℝ)^2) :
    (1280*entropyScale α B β L/β)^((2*(d/4))^2) *
      ((n:ℝ)+1)^(min n ⌊K*d⌋₊) *
      (1+8*A*L*Real.sqrt d/entropyScale α B β L)^(min n ⌊K*d⌋₊) *
      (1+8*B*L/entropyScale α B β L)^n ≤ Real.exp (-(d:ℝ)^2) := by
  apply localized_entropy_product_le hα hα' hA hB hβ hK hL hd hn
  exact (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le (by positivity))

/-- An eventual statement with a fixed positive scale, with witnesses given by
`entropyScale` and the deterministic natural number `entropyCutoff`. -/
theorem exists_localized_entropy_decay {α A B β K L : ℝ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K) (hL : 0 < L) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ d₀ : ℕ, ∀ d n : ℕ, d₀ ≤ d →
      (n:ℝ) ≤ α*(d:ℝ)^2 →
      (1280*c/β)^((2*(d/4))^2) * ((n:ℝ)+1)^(min n ⌊K*d⌋₊) *
        (1+8*A*L*Real.sqrt d/c)^(min n ⌊K*d⌋₊) *
        (1+8*B*L/c)^n ≤ Real.exp (-(d:ℝ)^2) := by
  obtain ⟨hg, hC0, hell, hc, hc1, hC1⟩ := entropy_constants hα hα' hA hB hβ hL
  exact ⟨entropyScale α B β L, hc, hc1, entropyCutoff α A B β K L,
    fun d n hd hn => localized_entropy_min_floor_le hα hα' hA hB hβ hK hL hd hn⟩

/-- The exact finite binomial sum is bounded by the crude product used above. -/
theorem entropy_binomial_sum_le (n m : ℕ) {H T : ℝ} (hH : 1 ≤ H) (hT : 1 ≤ T) :
    (∑ s ∈ Finset.range (m+1), (n.choose s:ℝ)*H^s*T^(n-s)) ≤
      ((n:ℝ)+1)^m*H^m*T^n := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hchoose : (∑ s ∈ Finset.range (m+1), (n.choose s:ℝ)) ≤ ((n:ℝ)+1)^m := by
    exact_mod_cast sum_choose_le_successor_pow n m
  calc
    _ ≤ ∑ s ∈ Finset.range (m+1), (n.choose s:ℝ)*H^m*T^n := by
      apply Finset.sum_le_sum
      intro s hs
      have hsm : s ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
      have hh := pow_le_pow_right₀ hH hsm
      have ht := pow_le_pow_right₀ hT (Nat.sub_le n s)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)) ht
        (pow_nonneg hT0 _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hH0 _))
    _ = (∑ s ∈ Finset.range (m+1), (n.choose s:ℝ))*H^m*T^n := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hchoose (pow_nonneg hH0 _)) (pow_nonneg hT0 _)

/-- Direct support-family reduction, with no binomial enumeration premise. -/
theorem entropy_support_sum_le (n m : ℕ) {H T : ℝ} (hH : 1 ≤ H) (hT : 1 ≤ T) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card ≤ m),
      H^I.card*T^(n-I.card)) ≤ ((n:ℝ)+1)^m*H^m*T^n := by
  classical
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  let S := (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card ≤ m)
  have hcard : (S.card:ℝ) ≤ ((n:ℝ)+1)^m := by
    have := card_small_supports_le (Finset.univ : Finset (Fin n)) m
    simpa [S] using (Nat.cast_le (α:=ℝ)).mpr this
  change (∑ I ∈ S, H^I.card*T^(n-I.card)) ≤ _
  calc
    _ ≤ ∑ I ∈ S, H^m*T^n := by
      apply Finset.sum_le_sum
      intro I hI
      have hsm : I.card ≤ m := (Finset.mem_filter.mp hI).2
      exact mul_le_mul (pow_le_pow_right₀ hH hsm)
        (pow_le_pow_right₀ hT (Nat.sub_le n I.card))
        (pow_nonneg hT0 _) (pow_nonneg hH0 _)
    _ = (S.card:ℝ)*H^m*T^n := by simp [mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard (pow_nonneg hH0 _)) (pow_nonneg hT0 _)

/-- The original finite-dimensional binomial entropy bound decays at the same
explicit scale and deterministic natural cutoff. -/
theorem localized_entropy_binomial_le {α A B β K L : ℝ} {d n : ℕ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K) (hL : 0 < L)
    (hd : entropyCutoff α A B β K L ≤ d) (hn : (n:ℝ) ≤ α*(d:ℝ)^2) :
    (1280*entropyScale α B β L/β)^((2*(d/4))^2) *
      (∑ s ∈ Finset.range (min n ⌊K*d⌋₊+1), (n.choose s:ℝ)*
        (1+8*A*L*Real.sqrt d/entropyScale α B β L)^s *
        (1+8*B*L/entropyScale α B β L)^(n-s)) ≤ Real.exp (-(d:ℝ)^2) := by
  have hc : 0 < entropyScale α B β L := Real.exp_pos _
  have hH : 1 ≤ 1+8*A*L*Real.sqrt d/entropyScale α B β L :=
    le_add_of_nonneg_right (by positivity)
  have hT : 1 ≤ 1+8*B*L/entropyScale α B β L := le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ (1280*entropyScale α B β L/β)^((2*(d/4))^2) *
        (((n:ℝ)+1)^(min n ⌊K*d⌋₊) *
        (1+8*A*L*Real.sqrt d/entropyScale α B β L)^(min n ⌊K*d⌋₊) *
        (1+8*B*L/entropyScale α B β L)^n) :=
      mul_le_mul_of_nonneg_left (entropy_binomial_sum_le _ _ hH hT) (by positivity)
    _ ≤ _ := by
      simpa only [mul_assoc] using
        localized_entropy_min_floor_le hα hα' hA hB hβ hK hL hd hn

end GaussianEllipsoid
