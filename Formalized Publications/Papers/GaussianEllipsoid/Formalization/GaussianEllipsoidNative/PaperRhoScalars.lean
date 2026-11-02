import CutoffGeometry

noncomputable section
open Finset Filter
namespace GaussianEllipsoidCandidate

/-- The source's floor-half residual-rank margin holds uniformly from d=8.
No divisibility or even-dimension convention is introduced. -/
theorem rho_floor_half_margin (rho : ℝ) (hrho : rho < 1/8) (d : ℕ) (hd : 8 ≤ d) :
    (d:ℝ)/4 ≤ (d/2:ℕ)-rho*(d:ℝ) := by
  have hm : d%2 < 2 := Nat.mod_lt d (by omega)
  have he := Nat.mod_add_div d 2
  have he' : (d%2:ℕ)+(2:ℝ)*(d/2:ℕ)=(d:ℝ) := by exact_mod_cast he
  have hm' : ((d%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast (show d%2 ≤ 1 by omega)
  have hd' : (8:ℝ) ≤ d := by exact_mod_cast hd
  have hr := mul_lt_mul_of_pos_right hrho (show (0:ℝ)<d by positivity)
  nlinarith

/-- From the paper's rank-loss statement, the exact c_rank=1/4 premise follows. -/
theorem rho_residual_rank_margin (rho : ℝ) (hrho : rho < 1/8) (d r : ℕ) (hd : 8 ≤ d)
    (hr : (d/2:ℕ)-rho*(d:ℝ) ≤ (r:ℝ)) : (d:ℝ)/4 ≤ (r:ℝ) :=
  (rho_floor_half_margin rho hrho d hd).trans hr

/-- The displayed source upper effective-support cap uses exactly32q² in the
choice of rho and16q² in the group estimate. -/
theorem rho_effective_support_cap (q rho cup d S R : ℝ)
    (hq : 1 < q) (hrho : 0 < rho) (hcap : rho < cup/(32*q^2)) (hd : 0 < d)
    (hS : S ≤ rho*d) (hR : R ≤ 16*q^2*S) : R < cup*d := by
  have hqpos : 0 < q := by linarith
  have hh := (lt_div_iff₀ (by positivity : 0 < 32*q^2)).mp hcap
  have hc : 0 < cup := by nlinarith [sq_pos_of_pos hqpos]
  have hs := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 16*q^2)
  have hhd := mul_lt_mul_of_pos_right hh hd
  nlinarith [mul_pos hc hd]

/-- First-late source scale from the actual cumulative support bound. -/
theorem rho_first_late_scale (q T rho d S H : ℝ)
    (hq : 1 < q) (hT : 0 < T) (hrho : 0 < rho)
    (hcut : rho*d < H) (hthrough : H ≤ T*q^2/(q-1)*S) :
    rho*(q-1)/(T*q^2)*d < S := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q-1 := by linarith
  have hden : 0 < T*q^2 := by positivity
  have hh := hcut.trans_le hthrough
  have hh' := mul_lt_mul_of_pos_right hh hqm
  have he : (T*q^2/(q-1)*S)*(q-1)=T*q^2*S := by field_simp <;> try ring
  rw [he] at hh'
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hden).mpr
  nlinarith

/-- Geometric record growth for every real q>1, on the actual finite index range. -/
theorem finite_real_growth_power (q : ℝ) (hq : 0 ≤ q) (S : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ r,r+1<N → q*S r≤S (r+1)) (p n : ℕ) (hpn : p+n<N) :
    q^n*S p≤S (p+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (by omega)
    have hs := hstep (p+n) (by omega)
    have hm := mul_le_mul_of_nonneg_left hp hq
    rw [pow_succ]
    have he : p+(n+1)=p+n+1 := by omega
    rw [he]
    nlinarith

/-- The literal logarithmic count is used in the paper only when a first late
group exists. This branch condition matters when K is arbitrarily small. -/
theorem rho_late_count_log (q T rho K d : ℝ) (hq : 1 < q) (hT : 0 < T)
    (hrho : 0 < rho) (hK : 0 < K) (hd : 0 < d)
    (S : ℕ → ℝ) (N p : ℕ) (hp : p<N)
    (hstep : ∀ r,r+1<N → q*S r≤S (r+1))
    (hlate : rho*(q-1)/(T*q^2)*d < S p)
    (hupper : ∀ r<N,S r≤K*d) :
    ((N-p:ℕ):ℝ) ≤ 1+Real.log ((q^2/(q-1))*K*T/rho)/Real.log q := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q-1 := by linarith
  have hlq : 0 < Real.log q := Real.log_pos hq
  let n := N-p-1
  have hn : p+n<N := by dsimp [n]; omega
  have hg := finite_real_growth_power q hq0.le S N hstep p n hn
  have hpow : 0 < q^n := pow_pos hq0 _
  have hprod := (mul_lt_mul_of_pos_left hlate hpow).trans_le (hg.trans (hupper _ hn))
  have hratio : q^n < (q^2/(q-1))*K*T/rho := by
    have hden : 0 < T*q^2 := by positivity
    have hcancel : q^n*(rho*(q-1)/(T*q^2)*d) =
        (q^n*rho*(q-1)*d)/(T*q^2) := by ring
    rw [hcancel] at hprod
    have hm := (div_lt_iff₀ hden).mp hprod
    have hcan : q^n*rho*(q-1) < K*(T*q^2) := by nlinarith
    have he : (q^2/(q-1))*K*T/rho=(K*(T*q^2))/(rho*(q-1)) := by field_simp <;> try ring
    rw [he]
    apply (lt_div_iff₀ (by positivity : 0 < rho*(q-1))).mpr
    nlinarith
  have hlogs := Real.log_le_log hpow hratio.le
  rw [Real.log_pow] at hlogs
  have hni := (le_div_iff₀ hlq).mpr hlogs
  have hcast : ((N-p:ℕ):ℝ)=(n:ℝ)+1 := by
    have he : N-p=n+1 := by dsimp [n]; omega
    exact_mod_cast he
  rw [hcast]
  linarith

/-- The logarithmic effective-support lower threshold follows eventually for
any fixed positive constants, with their full parameter dependence retained. -/
theorem eventually_log_le_mul_div_log (c C : ℝ) (hc : 0<c) (hC : 0<C) :
    ∀ᶠ d : ℝ in atTop,C*Real.log d ≤ c*d/Real.log d := by
  have he := (Real.isLittleO_pow_log_id_atTop (n:=2)).bound (div_pos hc hC)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with d he hd
  have hd0 : 0<d := by linarith
  have hl : 0<Real.log d := Real.log_pos hd
  have he' : (Real.log d)^2 ≤ (c/C)*d := by
    simpa only [Real.norm_eq_abs,id_eq,abs_of_nonneg (sq_nonneg (Real.log d)),abs_of_pos hd0] using he
  have hm : C*(Real.log d)^2≤c*d := calc
    _ ≤ C*((c/C)*d) := mul_le_mul_of_nonneg_left he' hC.le
    _ = _ := by field_simp
  apply (le_div_iff₀ hl).mpr
  nlinarith

theorem eventually_nat_log_le_mul_div_log (c C : ℝ) (hc : 0<c) (hC : 0<C) :
    ∀ᶠ d : ℕ in atTop,C*Real.log (d:ℝ) ≤ c*(d:ℝ)/Real.log (d:ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (eventually_log_le_mul_div_log c C hc hC)

/-- For every positive rho the concrete sparse prefix budget is eventually
below rho*d, without fixing rho to the historical numerical implementation. -/
theorem eventually_sparse_budget_le_rho (rho : ℝ) (hrho : 0<rho) :
    ∀ᶠ d : ℝ in atTop,(⌊d/(8192*Real.log d)⌋₊:ℝ) ≤ rho*d := by
  have he := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1/(8192*rho)))
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with d he hd
  have hd0 : 0<d := by linarith
  have hl : 0<Real.log d := Real.log_pos hd
  have hm : 1 ≤ 8192*rho*Real.log d := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0<8192*rho)).mp he
  have hf := Nat.floor_le (by positivity : 0≤d/(8192*Real.log d))
  apply hf.trans
  apply (div_le_iff₀ (by positivity : 0<8192*Real.log d)).mpr
  nlinarith

#print axioms rho_floor_half_margin
#print axioms rho_effective_support_cap
#print axioms rho_first_late_scale
#print axioms rho_late_count_log
#print axioms eventually_nat_log_le_mul_div_log
#print axioms eventually_sparse_budget_le_rho
end GaussianEllipsoidCandidate
