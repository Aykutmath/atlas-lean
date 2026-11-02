import ActualCoefficientNets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter
namespace GaussianEllipsoidCandidate

/-- The exact d log d entropy exponent is negligible relative to d²/log d. -/
theorem eventually_multiscale_entropy_absorption (H b : ℝ) (hH : 0 < H) (hb : 0 < b) :
    ∀ᶠ d : ℝ in atTop, 1 < d ∧ H*d*Real.log d ≤ (b/2)*d^2/Real.log d := by
  have ht : Tendsto (fun d : ℝ => Real.log d ^ 2 / d) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have he := ht.eventually_lt_const (div_pos hb (by positivity : 0 < 2*H))
  filter_upwards [he, eventually_gt_atTop (1:ℝ)] with d he hd
  have hd0 : 0 < d := by linarith
  have hl : 0 < Real.log d := Real.log_pos hd
  have he' : Real.log d ^ 2 < b/(2*H)*d := (div_lt_iff₀ hd0).mp he
  refine ⟨hd, (le_div_iff₀ hl).mpr ?_⟩
  have hmul := mul_le_mul_of_nonneg_left he'.le (show 0 ≤ H*d by positivity)
  have heq : H*d*(b/(2*H)*d) = (b/2)*d^2 := by field_simp <;> ring
  rw [heq] at hmul
  nlinarith only [hmul]

/-- Support and coefficient entropy, together with any fixed polynomial prefactor,
is absorbed by the actual fixed-vector d²/log d tail uniformly for n≤Ad², m≤Kd. -/
theorem eventually_multiscale_net_tail (A K B C b : ℝ) (a : ℕ)
    (hA : 0 < A) (hK : 0 ≤ K) (hB : 1 ≤ B) (hC : 0 < C) (hb : 0 < b) :
    ∀ᶠ d : ℕ in atTop, ∀ n m : ℕ, (n:ℝ) ≤ A*(d:ℝ)^2 → (m:ℝ) ≤ K*d →
      (B*(n+1))^m * (C*(n+1)^a*Real.exp (-b*(d:ℝ)^2/Real.log d)) ≤
        Real.exp (-(b/2)*(d:ℝ)^2/Real.log d) := by
  let H : ℝ := 3*K+1+3*a
  have hH : 0 < H := by dsimp [H]; positivity
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop).eventually
    (eventually_multiscale_entropy_absorption H b hH hb)
  have hcut := (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (max C (B*(A+1))))
  filter_upwards [he, hcut] with d he hcut
  intro n m hn hm
  have hd : (1:ℝ) < d := he.1
  have hd0 : (0:ℝ) < d := by linarith
  have hl : 0 < Real.log (d:ℝ) := Real.log_pos hd
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hnp : 0 < (n:ℝ)+1 := by positivity
  have hn1 : (n:ℝ)+1 ≤ (A+1)*(d:ℝ)^2 := by nlinarith [sq_nonneg ((d:ℝ)-1)]
  have hbD : B*((n:ℝ)+1) ≤ (d:ℝ)^3 := by
    calc
      _ ≤ B*((A+1)*(d:ℝ)^2) := mul_le_mul_of_nonneg_left hn1 hB0.le
      _ = (B*(A+1))*(d:ℝ)^2 := by ring
      _ ≤ (d:ℝ)*(d:ℝ)^2 := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hcut) (sq_nonneg _)
      _ = _ := by ring
  have hnD : (n:ℝ)+1 ≤ (d:ℝ)^3 :=
    (le_mul_of_one_le_left hnp.le hB).trans hbD
  have hlogB : Real.log (B*((n:ℝ)+1)) ≤ 3*Real.log (d:ℝ) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (mul_pos hB0 hnp) hbD
  have hlogn : Real.log ((n:ℝ)+1) ≤ 3*Real.log (d:ℝ) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hnp hnD
  have hlogC : Real.log C ≤ Real.log (d:ℝ) := Real.log_le_log hC ((le_max_left _ _).trans hcut)
  have hmterm : (m:ℝ)*Real.log (B*((n:ℝ)+1)) ≤ 3*K*(d:ℝ)*Real.log d := by
    have h₁ := mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg m)
    have h₂ := mul_le_mul_of_nonneg_right hm (show 0 ≤ 3*Real.log (d:ℝ) by positivity)
    nlinarith only [h₁,h₂]
  have hpref : Real.log C+(a:ℝ)*Real.log ((n:ℝ)+1) ≤ (1+3*a)*(d:ℝ)*Real.log d := by
    have ha := mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg a)
    have hdd := mul_le_mul_of_nonneg_right hd.le (show 0 ≤ (1+3*(a:ℝ))*Real.log d by positivity)
    nlinarith only [ha,hlogC,hdd]
  have htotal : (m:ℝ)*Real.log (B*((n:ℝ)+1))+Real.log C+
      (a:ℝ)*Real.log ((n:ℝ)+1) ≤ (b/2)*(d:ℝ)^2/Real.log d := by
    have hh := he.2
    dsimp [H] at hh
    nlinarith only [hmterm,hpref,hh]
  calc
    _ = Real.exp ((m:ℝ)*Real.log (B*((n:ℝ)+1))+Real.log C+
        (a:ℝ)*Real.log ((n:ℝ)+1)-b*(d:ℝ)^2/Real.log d) := by
      simp only [sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul,
        Real.exp_log (mul_pos hB0 hnp), Real.exp_log hC, Real.exp_log hnp, neg_div,
        neg_mul]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      convert sub_le_sub_right htotal (b*(d:ℝ)^2/Real.log d) using 1 <;> ring)

/-- The remaining explicit exponential upper bound tends to zero. -/
theorem multiscale_exponential_tendsto_zero (b : ℝ) (hb : 0 < b) :
    Tendsto (fun d : ℕ => Real.exp (-b*(d:ℝ)^2/Real.log d)) atTop (nhds 0) := by
  have hg : Tendsto (fun d : ℕ => b*(d:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hb
  have hf : Tendsto (fun d : ℕ => b*(d:ℝ)^2/Real.log d) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ hg
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop).eventually
      (eventually_gt_atTop (1:ℝ))] with d hd
    have hl : 0 < Real.log (d:ℝ) := Real.log_pos hd
    apply (le_div_iff₀ hl).mpr
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg d))
      (show 0 ≤ b*(d:ℝ) by positivity)
    nlinarith only [hh]
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hf using 1
  ext d
  congr 1
  ring

end GaussianEllipsoidCandidate
