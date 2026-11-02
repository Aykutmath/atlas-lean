import LateGroupCount

namespace GaussianEllipsoidCandidate

/-- A self-contained elementary power bound used to select an integer width. -/
theorem natCast_le_two_pow (n : ℕ) : (n:ℝ) ≤ (2:ℝ)^n := by
  have h : ∀ n : ℕ, (n:ℝ)+1 ≤ (2:ℝ)^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      push_cast
      nlinarith
  linarith [h n]

/-- Polynomially many retained offsets have exponentially tiny omitted mass. -/
theorem retention_error_scaled (K : ℝ) (hK : 1 ≤ K) :
    (8*(1/2:ℝ)^(40+4*⌈K⌉₊))*K^2 ≤ (1/2:ℝ)^37 := by
  let n := ⌈K⌉₊
  have hK0 : 0 ≤ K := by linarith
  have hKn : K ≤ (2:ℝ)^n := (Nat.le_ceil K).trans (natCast_le_two_pow n)
  have ha : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
  have hpow : K^2 ≤ ((2:ℝ)^n)^4 := by
    nlinarith [sq_nonneg ((2:ℝ)^n-1), sq_nonneg (K-(2:ℝ)^n)]
  have hprod : (1/2:ℝ)^n * (2:ℝ)^n = 1 := by rw [← mul_pow]; norm_num
  have hcancel : (1/2:ℝ)^(4*n) * ((2:ℝ)^n)^4 = 1 := by
    rw [Nat.mul_comm 4 n, pow_mul, ← mul_pow, hprod]
    norm_num
  have hb : (1/2:ℝ)^(4*n)*K^2 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ (1/2)^ (4*n))
    rwa [hcancel] at hh
  have heq : 8*(1/2:ℝ)^(40+4*n) = (1/2:ℝ)^37*(1/2:ℝ)^(4*n) := by
    rw [pow_add]
    norm_num
    ring
  change (8*(1/2:ℝ)^(40+4*n))*K^2 ≤ _
  rw [heq, mul_assoc]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (mul_one _)

/-- The explicit target denominator is no larger than `K²`. -/
theorem target_denominator_bounds (K : ℝ) (hK : 1 ≤ K) :
    0 < Real.sqrt K*(1+Real.log K) ∧
      Real.sqrt K*(1+Real.log K) ≤ K^2 := by
  have hK0 : 0 < K := by linarith
  have hlog := Real.log_nonneg hK
  have hlogup := Real.log_le_sub_one_of_pos hK0
  have hsqrt : Real.sqrt K ≤ K := Real.sqrt_le_iff.mpr ⟨hK0.le, by nlinarith⟩
  refine ⟨mul_pos (Real.sqrt_pos.mpr hK0) (by linarith), ?_⟩
  calc
    Real.sqrt K*(1+Real.log K) ≤ K*K :=
      mul_le_mul hsqrt (by linarith) (by linarith) hK0.le
    _ = K^2 := by ring

/-- Constants after using measurable half-witnesses. The retained lower
constant is `(2^-22 / sqrt 2)/(sqrt K * J)`. All tail absorption inequalities
and the unchanged `2^-29` fixed-vector scale follow with `J ≤ 17(1+log K)`. -/
theorem projected_retained_tail_constants (K J : ℝ) (hK : 1 ≤ K)
    (hJ : 0 < J) (hJup : J ≤ 17*(1+Real.log K)) :
    let ε := 8*(1/2:ℝ)^(40+4*⌈K⌉₊)
    let c := ((1/2:ℝ)^22/Real.sqrt 2)/(Real.sqrt K*J)
    ε ≤ 1/2 ∧ 2*ε ≤ c/4 ∧
      ((1/2:ℝ)^29)/(Real.sqrt K*(1+Real.log K)) ≤ c/4 ∧
      ((1/2:ℝ)^29)/(Real.sqrt K*(1+Real.log K)) ≤ c*(1-ε)-2*ε := by
  dsimp only
  let ε := 8*(1/2:ℝ)^(40+4*⌈K⌉₊)
  let c := ((1/2:ℝ)^22/Real.sqrt 2)/(Real.sqrt K*J)
  let D := Real.sqrt K*(1+Real.log K)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hs2 : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2up : Real.sqrt (2:ℝ) ≤ 3/2 := Real.sqrt_le_iff.mpr (by norm_num)
  have hD := target_denominator_bounds K hK
  have hscale := retention_error_scaled K hK
  change ε*K^2 ≤ (1/2:ℝ)^37 at hscale
  have hεsmall : ε ≤ (1/2:ℝ)^37 := by
    have hsq : 1 ≤ K^2 := by nlinarith
    nlinarith
  have hεhalf : ε ≤ 1/2 := by norm_num at hεsmall ⊢; linarith
  have hJpos : 0 < Real.sqrt K*J := mul_pos hsK hJ
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hdenom : Real.sqrt K*J ≤ 17*D := by
    have hm := mul_le_mul_of_nonneg_left hJup hsK.le
    dsimp [D]
    nlinarith
  have hdenomK : Real.sqrt K*J ≤ 17*K^2 := by
    dsimp [D] at hdenom
    linarith [hD.2]
  have hcdenom : c*(Real.sqrt K*J) = (1/2:ℝ)^22/Real.sqrt 2 := by
    dsimp [c]
    field_simp
    <;> ring
  have hsmall : 8*ε*(Real.sqrt K*J) ≤ (1/2:ℝ)^22/Real.sqrt 2 := by
    have he := mul_le_mul_of_nonneg_left hdenomK (by positivity : 0 ≤ 8*ε)
    have hnum : 8*ε*(Real.sqrt K*J) ≤ 136*(1/2:ℝ)^37 := by nlinarith
    have hconst : 136*(1/2:ℝ)^37 ≤ (1/2:ℝ)^22/Real.sqrt 2 := by
      apply (le_div_iff₀ hs2).2
      norm_num at hs2up ⊢
      nlinarith
    exact hnum.trans hconst
  have habsorb : 2*ε ≤ c/4 := by nlinarith
  have hfix : ((1/2:ℝ)^29)/D ≤ c/4 := by
    apply (div_le_iff₀ hD.1).2
    have hcD : ((1/2:ℝ)^22/Real.sqrt 2) ≤ c*(17*D) := by
      rw [← hcdenom]
      exact mul_le_mul_of_nonneg_left hdenom hc0.le
    have hconst : (1/2:ℝ)^29*68 ≤ (1/2:ℝ)^22/Real.sqrt 2 := by
      apply (le_div_iff₀ hs2).2
      norm_num at hs2up ⊢
      nlinarith
    nlinarith
  refine ⟨hεhalf, habsorb, hfix, ?_⟩
  exact hfix.trans (retained_tail_absorption c 2 ε hc0.le hεhalf habsorb)

/-- Common retained constant after taking the minimum of the verified
projected half-witness and macroscopic late-driver bounds. The sharper
absorption preserves the final fixed-vector constant `2^-29`. -/
theorem common_retained_tail_constants (K J : ℝ) (hK : 1 ≤ K)
    (hJ : 0 < J) (hJup : J ≤ 17*(1+Real.log K)) :
    let ε := 8*(1/2:ℝ)^(40+4*⌈K⌉₊)
    let c := (1/2:ℝ)^24/(Real.sqrt K*J)
    ε ≤ 1/8 ∧ 2*ε ≤ c/8 ∧
      3*c/4 ≤ c*(1-ε)-2*ε ∧
      ((1/2:ℝ)^29)/(Real.sqrt K*(1+Real.log K)) ≤ 3*c/4 ∧
      ((1/2:ℝ)^29)/(Real.sqrt K*(1+Real.log K)) ≤ c*(1-ε)-2*ε := by
  dsimp only
  let ε := 8*(1/2:ℝ)^(40+4*⌈K⌉₊)
  let c := (1/2:ℝ)^24/(Real.sqrt K*J)
  let D := Real.sqrt K*(1+Real.log K)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hD := target_denominator_bounds K hK
  have hscale := retention_error_scaled K hK
  change ε*K^2 ≤ (1/2:ℝ)^37 at hscale
  have hεsmall : ε ≤ (1/2:ℝ)^37 := by
    have hsq : 1 ≤ K^2 := by nlinarith
    nlinarith
  have hεeighth : ε ≤ 1/8 := by norm_num at hεsmall ⊢; linarith
  have hJpos : 0 < Real.sqrt K*J := mul_pos hsK hJ
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hdenom : Real.sqrt K*J ≤ 17*D := by
    have hm := mul_le_mul_of_nonneg_left hJup hsK.le
    dsimp [D]
    nlinarith
  have hdenomK : Real.sqrt K*J ≤ 17*K^2 := by
    dsimp [D] at hdenom
    linarith [hD.2]
  have hcdenom : c*(Real.sqrt K*J) = (1/2:ℝ)^24 := by
    dsimp [c]
    exact div_mul_cancel₀ _ hJpos.ne'
  have hsmall : 16*ε*(Real.sqrt K*J) ≤ (1/2:ℝ)^24 := by
    have he := mul_le_mul_of_nonneg_left hdenomK (by positivity : 0 ≤ 16*ε)
    have hnum : 16*ε*(Real.sqrt K*J) ≤ 272*(1/2:ℝ)^37 := by nlinarith
    have hconst : 272*(1/2:ℝ)^37 ≤ (1/2:ℝ)^24 := by norm_num
    exact hnum.trans hconst
  have habsorb : 2*ε ≤ c/8 := by nlinarith
  have hret : 3*c/4 ≤ c*(1-ε)-2*ε := by nlinarith
  have hfix : ((1/2:ℝ)^29)/D ≤ 3*c/4 := by
    apply (div_le_iff₀ hD.1).2
    have hcD : (1/2:ℝ)^24 ≤ c*(17*D) := by
      rw [← hcdenom]
      exact mul_le_mul_of_nonneg_left hdenom hc0.le
    have hconst : (1/2:ℝ)^29*68 ≤ 3*(1/2:ℝ)^24 := by norm_num
    nlinarith
  exact ⟨hεeighth, habsorb, hret, hfix, hfix.trans hret⟩

end GaussianEllipsoidCandidate
