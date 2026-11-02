/-
E1 helper H-volume + H-nets: Euclidean ball volume bound and volumetric net bounds.

Mathematical source: paper.tex l992-997 (volume of an `R`-ball in `R^m` is at
most `(CR/√m)^m`) and l1308-1324 (volumetric covering/packing bounds
`(1+2R/r)^m`).

The clean constant `√(2πe)` is the constant from the Gaussian-integration upper
bound: with `σ² = R²/m`,
`vol(B_R) ≤ e^{R²/2σ²}(2πσ²)^{m/2} = (√(2πe)·R/√m)^m`.
Here it is derived from Mathlib's exact ball-volume formula
(`EuclideanSpace.volume_ball`) plus elementary lower bounds on `Γ` at integers
(`k! ≥ (k/e)^k`) and half-integers (`Γ(k+3/2)² ≥ ((k+1/2)/e)^{2k+1}`), avoiding
any probability or multidimensional integration.

No overlap with existing pieces: `NormBridges.lean` (norms, Cauchy-Schwarz,
`euclidNorm_eq_norm_toLp`) and `Discretize.lean` (operator-norm discretization)
contain no volume or net-cardinality lemmas (checked 2026-10-01). This file
reuses `euclidNorm` and `euclidNorm_eq_norm_toLp` from `NormBridges`.

Integration: this file is already in `namespace GaussianEllipsoid` and imports
`GaussianEllipsoid.NormBridges`; to integrate, move it into `GaussianEllipsoid/`.
-/
import GaussianEllipsoid.NormBridges
import Mathlib

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory

/-! ### Clean constant -/

/-- Clean constant for the Euclidean volume bound: `√(2πe)`. -/
def euclidVolConst : ℝ := Real.sqrt (2 * Real.pi * Real.exp 1)

theorem euclidVolConst_sq : euclidVolConst ^ 2 = 2 * Real.pi * Real.exp 1 := by
  unfold euclidVolConst
  apply Real.sq_sqrt
  exact mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) (Real.exp_pos 1).le

theorem euclidVolConst_nonneg : 0 ≤ euclidVolConst := by
  unfold euclidVolConst
  exact Real.sqrt_nonneg _

/-! ### Exponential estimate -/

/-- `(1 + 1/t)^j ≤ exp (j * (1/t))`, from `1 + s ≤ exp s`. -/
theorem pow_one_add_inv_le_exp (t : ℝ) (ht : 0 < t) (j : ℕ) :
    (1 + 1 / t) ^ j ≤ Real.exp ((j : ℝ) * (1 / t)) := by
  have h1 : (0 : ℝ) ≤ 1 + 1 / t := by
    have h2 : (0 : ℝ) < 1 / t := one_div_pos.mpr ht
    linarith
  have h2 : (1 : ℝ) + 1 / t ≤ Real.exp (1 / t) := by
    have h := Real.add_one_le_exp (1 / t)
    linarith
  calc (1 + 1 / t) ^ j ≤ (Real.exp (1 / t)) ^ j := pow_le_pow_left₀ h1 h2 j
    _ = Real.exp ((j : ℝ) * (1 / t)) := (Real.exp_nat_mul (1 / t) j).symm

/-! ### Factorial lower bound (even dimensions) -/

/-- `k! ≥ (k/e)^k`: `(k:ℝ)^k ≤ e^k * k!`, by induction using
`(1 + 1/k)^k ≤ e`. -/
theorem nat_factorial_ge (k : ℕ) :
    (k : ℝ) ^ k ≤ (Real.exp 1) ^ k * ((k.factorial : ℕ) : ℝ) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have h2 : (2 : ℝ) ≤ Real.exp 1 := by
          have h := Real.add_one_le_exp (1 : ℝ)
          linarith
        simp only [zero_add, Nat.cast_one, pow_one, Nat.factorial_one, mul_one]
        linarith
      · have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
        have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
        have hK1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        have hfact : (((k + 1).factorial : ℕ) : ℝ)
            = ((k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        have hexp : (Real.exp 1) ^ (k + 1)
            = (Real.exp 1) ^ k * Real.exp 1 :=
          pow_succ _ _
        have hlhs : (((k + 1 : ℕ) : ℝ)) ^ (k + 1)
            = (((k : ℝ) + 1)) ^ k * ((k : ℝ) + 1) := by
          rw [hK1]
          exact pow_succ _ _
        rw [hlhs, hexp, hfact]
        have hmain : ((k : ℝ) + 1) ^ k
            ≤ ((Real.exp 1) ^ k * Real.exp 1) * ((k.factorial : ℕ) : ℝ) := by
          have hKK : (k : ℝ) * ((1 : ℝ) + 1 / (k : ℝ)) = (k : ℝ) + 1 := by
            rw [mul_add, mul_one, mul_one_div, div_self hkne]
          have hsplit : ((k : ℝ) + 1) ^ k
              = (k : ℝ) ^ k * (1 + 1 / (k : ℝ)) ^ k := by
            have hKKk : ((k : ℝ) + 1) ^ k
                = ((k : ℝ) * (1 + 1 / (k : ℝ))) ^ k := by
              rw [hKK]
            rw [hKKk, mul_pow]
          have hkk1 : (k : ℝ) * (1 / (k : ℝ)) = 1 := by
            rw [mul_one_div, div_self hkne]
          have hsub : (1 + 1 / (k : ℝ)) ^ k ≤ Real.exp 1 := by
            have h := pow_one_add_inv_le_exp (k : ℝ) hkR k
            rw [hkk1] at h
            exact h
          have hpos1 : (0 : ℝ) ≤ (1 + 1 / (k : ℝ)) ^ k := by
            apply pow_nonneg
            have h2 : (0 : ℝ) < 1 / (k : ℝ) := one_div_pos.mpr hkR
            linarith
          have hpos2 : (0 : ℝ) ≤ (Real.exp 1) ^ k * ((k.factorial : ℕ) : ℝ) :=
            mul_nonneg (pow_nonneg (Real.exp_pos 1).le k) (Nat.cast_nonneg _)
          rw [hsplit]
          calc (k : ℝ) ^ k * (1 + 1 / (k : ℝ)) ^ k
              ≤ ((Real.exp 1) ^ k * ((k.factorial : ℕ) : ℝ)) * Real.exp 1 :=
                mul_le_mul ih hsub hpos1 hpos2
            _ = ((Real.exp 1) ^ k * Real.exp 1) * ((k.factorial : ℕ) : ℝ) := by
                ring
        calc ((k : ℝ) + 1) ^ k * ((k : ℝ) + 1)
            = ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ k := mul_comm _ _
          _ ≤ ((k : ℝ) + 1)
              * (((Real.exp 1) ^ k * Real.exp 1) * ((k.factorial : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hmain (by linarith [hkR])
          _ = ((Real.exp 1) ^ k * Real.exp 1)
              * (((k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ)) := by ring

/-! ### Half-integer Gamma lower bound (odd dimensions) -/

/-- `Γ(k+3/2)² ≥ ((k+1/2)/e)^{2k+1}`, by induction using
`(1 + 1/(k+1/2))^{2k+1} ≤ e²`. -/
theorem gamma_odd_sq_ge (k : ℕ) :
    (((k : ℝ) + 1 / 2) / Real.exp 1) ^ (2 * k + 1)
      ≤ (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2 := by
  induction k with
  | zero =>
      simp only [Nat.cast_zero, mul_zero, zero_add]
      have hG : Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
        have h1 : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
        rw [h1, Real.Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 by norm_num),
          Real.Gamma_one_half_eq]
        ring
      rw [hG, pow_one, div_pow, Real.sq_sqrt Real.pi_pos.le]
      have h22 : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [h22]
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have hpe : (2 : ℝ) ≤ Real.pi * Real.exp 1 := by
        have h3e : (3 : ℝ) * Real.exp 1 < Real.pi * Real.exp 1 :=
          mul_lt_mul_of_pos_right hpi hepos
        have h33 : (3 : ℝ) * 2.7182818283 < 3 * Real.exp 1 :=
          mul_lt_mul_of_pos_left he (by norm_num)
        linarith
      rw [div_le_iff₀ hepos]
      linarith [hpe]
  | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have ha_pos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by
        have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        linarith
      have hk32pos : (0 : ℝ) < (k : ℝ) + 3 / 2 := by linarith [ha_pos]
      have hG : Real.Gamma (((k + 1 : ℕ) : ℝ) + 3 / 2)
          = ((k : ℝ) + 3 / 2) * Real.Gamma ((k : ℝ) + 3 / 2) := by
        have harg : (((k + 1 : ℕ) : ℝ) + 3 / 2) = ((k : ℝ) + 3 / 2) + 1 := by
          rw [hcast]
          ring
        rw [harg, Real.Gamma_add_one (ne_of_gt hk32pos)]
      have hexp : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      have hbase' : (((k + 1 : ℕ) : ℝ) + 1 / 2) = (k : ℝ) + 3 / 2 := by
        rw [hcast]
        ring
      rw [hG, hexp, hbase']
      have hX : ((k : ℝ) + 1 / 2) + 1
          = ((k : ℝ) + 1 / 2) * (1 + 1 / ((k : ℝ) + 1 / 2)) := by
        have hane : ((k : ℝ) + 1 / 2) ≠ 0 := ne_of_gt ha_pos
        field_simp
      have hX3 : (k : ℝ) + 3 / 2 = ((k : ℝ) + 1 / 2) + 1 := by ring
      have hsub2 : (1 + 1 / ((k : ℝ) + 1 / 2)) ^ (2 * k + 1)
          ≤ (Real.exp 1) ^ 2 := by
        have h := pow_one_add_inv_le_exp ((k : ℝ) + 1 / 2) ha_pos (2 * k + 1)
        have h23 : ((2 * k + 1 : ℕ) : ℝ) * (1 / ((k : ℝ) + 1 / 2)) = 2 := by
          have hane : ((k : ℝ) + 1 / 2) ≠ 0 := ne_of_gt ha_pos
          push_cast
          field_simp
        rw [h23] at h
        have hx := Real.exp_nat_mul (1 : ℝ) 2
        have h21 : ((2 : ℕ) : ℝ) * 1 = 2 := by push_cast; ring
        rw [h21] at hx
        rw [hx] at h
        exact h
      have hle : (((k : ℝ) + 3 / 2) / Real.exp 1) ^ (2 * k + 1)
          ≤ (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2 * (Real.exp 1) ^ 2 := by
        have hbase : (((k : ℝ) + 3 / 2) / Real.exp 1)
            = ((((k : ℝ) + 1 / 2)) / Real.exp 1)
              * (1 + 1 / ((k : ℝ) + 1 / 2)) := by
          rw [hX3, hX]
          simp only [div_eq_mul_inv]
          ring
        rw [hbase, mul_pow]
        have hpos1 : (0 : ℝ) ≤ (1 + 1 / ((k : ℝ) + 1 / 2)) ^ (2 * k + 1) := by
          apply pow_nonneg
          have h2 : (0 : ℝ) < 1 / ((k : ℝ) + 1 / 2) := one_div_pos.mpr ha_pos
          linarith
        have hpos2 : (0 : ℝ) ≤ (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2 := sq_nonneg _
        exact mul_le_mul ih hsub2 hpos1 hpos2
      calc (((k : ℝ) + 3 / 2) / Real.exp 1) ^ ((2 * k + 1) + 2)
          = (((k : ℝ) + 3 / 2) / Real.exp 1) ^ (2 * k + 1)
            * (((k : ℝ) + 3 / 2) / Real.exp 1) ^ 2 := pow_add _ _ _
        _ ≤ ((Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2 * (Real.exp 1) ^ 2)
            * (((k : ℝ) + 3 / 2) / Real.exp 1) ^ 2 :=
            mul_le_mul hle (le_refl _) (sq_nonneg _) (mul_nonneg (sq_nonneg _)
              (pow_nonneg (Real.exp_pos 1).le 2))
        _ = (((k : ℝ) + 3 / 2) * Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2 := by
            rw [mul_pow]
            have he1ne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
            have he2ne : (Real.exp 1) ^ 2 ≠ 0 :=
              ne_of_gt (pow_pos (Real.exp_pos 1) 2)
            field_simp

/-! ### Real core inequality -/

/-- Real core of the volume bound:
`R^n * (√π^n / Γ(n/2+1)) ≤ (C*R/√n)^n`. -/
theorem core_volume_ineq (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 ≤ R) :
    R ^ n * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))
      ≤ (euclidVolConst * R / Real.sqrt (n : ℝ)) ^ n := by
  rcases eq_or_lt_of_le hR with rfl | hRpos
  · have hn0 : n ≠ 0 := ne_of_gt hn
    simp [zero_pow hn0]
  · have hRn : (0 : ℝ) < R ^ n := pow_pos hRpos n
    have hsqnpos : (0 : ℝ) < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
    have hC : (euclidVolConst * R / Real.sqrt (n : ℝ)) ^ n
        = (euclidVolConst / Real.sqrt (n : ℝ)) ^ n * R ^ n := by
      have heq : euclidVolConst * R / Real.sqrt (n : ℝ)
          = (euclidVolConst / Real.sqrt (n : ℝ)) * R := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [heq, mul_pow]
    rw [hC]
    have hmain : Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)
        ≤ (euclidVolConst / Real.sqrt (n : ℝ)) ^ n := by
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hk : 0 < k := by omega
        have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
        have hkk2 : k + k = 2 * k := by ring
        have harg : (((k + k : ℕ) : ℝ) / 2 + 1) = (k : ℝ) + 1 := by
          push_cast
          ring
        have hG : Real.Gamma (((k + k : ℕ) : ℝ) / 2 + 1)
            = ((k.factorial : ℕ) : ℝ) := by
          rw [harg]
          exact Real.Gamma_nat_eq_factorial k
        have hsqrt : Real.sqrt Real.pi ^ (k + k) = Real.pi ^ k := by
          rw [hkk2, pow_mul, Real.sq_sqrt Real.pi_pos.le]
        have hRHS : (euclidVolConst / Real.sqrt ((k + k : ℕ) : ℝ)) ^ (k + k)
            = (Real.pi * Real.exp 1 / (k : ℝ)) ^ k := by
          rw [hkk2]
          have hcast2 : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
          rw [hcast2, pow_mul]
          congr 1
          rw [div_pow, euclidVolConst_sq]
          have h2k0 : (0 : ℝ) ≤ 2 * (k : ℝ) :=
            mul_nonneg zero_le_two hkR.le
          rw [Real.sq_sqrt h2k0]
          have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
          have h2kne : 2 * (k : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hkne
          field_simp
        rw [hG, hsqrt, hRHS]
        have hfact := nat_factorial_ge k
        have hpek : (Real.pi * Real.exp 1 / (k : ℝ)) ^ k
            = (Real.pi ^ k * (Real.exp 1) ^ k) / (k : ℝ) ^ k := by
          rw [div_pow, mul_pow]
        rw [hpek]
        have h1 : (Real.pi ^ k * (Real.exp 1) ^ k) / (k : ℝ) ^ k
            = Real.pi ^ k * (((Real.exp 1) ^ k / (k : ℝ) ^ k)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        rw [h1]
        have h2 : Real.pi ^ k / ((k.factorial : ℕ) : ℝ)
            = Real.pi ^ k * (1 / ((k.factorial : ℕ) : ℝ)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        rw [h2]
        have hkk_pos : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkR k
        have hfact_pos : (0 : ℝ) < ((k.factorial : ℕ) : ℝ) :=
          Nat.cast_pos.mpr (Nat.factorial_pos k)
        have hsubgoal : 1 / ((k.factorial : ℕ) : ℝ)
            ≤ (Real.exp 1) ^ k / (k : ℝ) ^ k := by
          rw [div_le_iff₀ hfact_pos]
          have hmul : (Real.exp 1) ^ k / (k : ℝ) ^ k * ((k.factorial : ℕ) : ℝ)
              = ((Real.exp 1) ^ k * ((k.factorial : ℕ) : ℝ)) / (k : ℝ) ^ k := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
          rw [hmul, le_div_iff₀ hkk_pos, one_mul]
          exact hfact
        exact mul_le_mul_of_nonneg_left hsubgoal (pow_nonneg Real.pi_pos.le k)
      · have hMpos : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) :=
          Nat.cast_pos.mpr (by omega)
        have hGarg : (((2 * k + 1 : ℕ) : ℝ) / 2 + 1) = (k : ℝ) + 3 / 2 := by
          push_cast
          ring
        have hsqrt_odd : Real.sqrt Real.pi ^ (2 * k + 1)
            = Real.pi ^ k * Real.sqrt Real.pi := by
          rw [pow_add, pow_mul, Real.sq_sqrt Real.pi_pos.le, pow_one]
        have hC2 : (euclidVolConst / Real.sqrt ((2 * k + 1 : ℕ) : ℝ)) ^ 2
            = (2 * Real.pi * Real.exp 1) / ((2 * k + 1 : ℕ) : ℝ) := by
          rw [div_pow, euclidVolConst_sq,
            Real.sq_sqrt (Nat.cast_nonneg _)]
        have hLHS2 : (Real.pi ^ k * Real.sqrt Real.pi
              / Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2
            = Real.pi ^ (2 * k + 1) / (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, ← pow_mul, ← pow_succ]
          have hexp2 : k * 2 + 1 = 2 * k + 1 := by ring
          rw [hexp2]
        have hRHS2 : ((euclidVolConst / Real.sqrt ((2 * k + 1 : ℕ) : ℝ))
              ^ (2 * k + 1)) ^ 2
            = ((2 * Real.pi * Real.exp 1) / ((2 * k + 1 : ℕ) : ℝ))
              ^ (2 * k + 1) := by
          have hj2 : (2 * k + 1) * 2 = 2 * (2 * k + 1) := by ring
          rw [← pow_mul, hj2, pow_mul, hC2]
        have hsq : Real.pi ^ (2 * k + 1) / (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2
            ≤ ((2 * Real.pi * Real.exp 1) / ((2 * k + 1 : ℕ) : ℝ))
              ^ (2 * k + 1) := by
          have hGpos : (0 : ℝ) < Real.Gamma ((k : ℝ) + 3 / 2) :=
            Real.Gamma_pos_of_pos (by
              have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
              linarith)
          have hG2pos : (0 : ℝ) < (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2 :=
            pow_pos hGpos 2
          have hMne : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hMpos
          have he1ne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
          have hM2 : ((2 * k + 1 : ℕ) : ℝ) = 2 * ((k : ℝ) + 1 / 2) := by
            push_cast
            ring
          have hkey := gamma_odd_sq_ge k
          have hdecomp : Real.pi ^ (2 * k + 1)
              = ((2 * Real.pi * Real.exp 1) / ((2 * k + 1 : ℕ) : ℝ))
                ^ (2 * k + 1)
                * ((((2 * k + 1 : ℕ) : ℝ)) / (2 * Real.exp 1)) ^ (2 * k + 1) := by
            rw [← mul_pow]
            congr 1
            have h2ene : 2 * Real.exp 1 ≠ 0 :=
              mul_ne_zero (by norm_num) he1ne
            field_simp
          have hY : ((((2 * k + 1 : ℕ) : ℝ)) / (2 * Real.exp 1)) ^ (2 * k + 1)
              / (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2 ≤ 1 := by
            rw [div_le_one hG2pos]
            have hYeq : ((((2 * k + 1 : ℕ) : ℝ)) / (2 * Real.exp 1)) ^ (2 * k + 1)
                = (((k : ℝ) + 1 / 2) / Real.exp 1) ^ (2 * k + 1) := by
              congr 1
              rw [hM2]
              have h2ene : 2 * Real.exp 1 ≠ 0 :=
                mul_ne_zero (by norm_num) he1ne
              field_simp
            rw [hYeq]
            exact hkey
          rw [hdecomp]
          have hrewrite : ((2 * Real.pi * Real.exp 1) / ((2 * k + 1 : ℕ) : ℝ))
                ^ (2 * k + 1)
                * ((((2 * k + 1 : ℕ) : ℝ)) / (2 * Real.exp 1)) ^ (2 * k + 1)
                / (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2
              = ((2 * Real.pi * Real.exp 1) / ((2 * k + 1 : ℕ) : ℝ)) ^ (2 * k + 1)
                * (((((2 * k + 1 : ℕ) : ℝ)) / (2 * Real.exp 1)) ^ (2 * k + 1)
                  / (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2) := by
            simp only [div_eq_mul_inv]
            ring
          rw [hrewrite]
          calc ((2 * Real.pi * Real.exp 1) / ((2 * k + 1 : ℕ) : ℝ)) ^ (2 * k + 1)
                * (((((2 * k + 1 : ℕ) : ℝ)) / (2 * Real.exp 1)) ^ (2 * k + 1)
                  / (Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2)
              ≤ ((2 * Real.pi * Real.exp 1) / ((2 * k + 1 : ℕ) : ℝ)) ^ (2 * k + 1)
                * 1 :=
                mul_le_mul_of_nonneg_left hY (pow_nonneg
                  (div_nonneg (mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le)
                    (Real.exp_pos 1).le) hMpos.le) _)
            _ = ((2 * Real.pi * Real.exp 1) / ((2 * k + 1 : ℕ) : ℝ))
                ^ (2 * k + 1) :=
                mul_one _
        rw [hsqrt_odd, hGarg]
        have hLHSnn : (0 : ℝ) ≤ Real.pi ^ k * Real.sqrt Real.pi
            / Real.Gamma ((k : ℝ) + 3 / 2) :=
          div_nonneg (mul_nonneg (pow_nonneg Real.pi_pos.le k)
            (Real.sqrt_nonneg _))
            (Real.Gamma_pos_of_pos (by
              have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
              linarith)).le
        have hRHSnn : (0 : ℝ)
            ≤ (euclidVolConst / Real.sqrt ((2 * k + 1 : ℕ) : ℝ)) ^ (2 * k + 1) :=
          pow_nonneg (div_nonneg euclidVolConst_nonneg (Real.sqrt_nonneg _)) _
        have hsq' : (Real.pi ^ k * Real.sqrt Real.pi
              / Real.Gamma ((k : ℝ) + 3 / 2)) ^ 2
            ≤ ((euclidVolConst / Real.sqrt ((2 * k + 1 : ℕ) : ℝ))
              ^ (2 * k + 1)) ^ 2 := by
          rw [hLHS2, hRHS2]
          exact hsq
        have habs := abs_le_of_sq_le_sq hsq' hRHSnn
        rw [abs_of_nonneg hLHSnn] at habs
        exact habs
    have hRn0 : (0 : ℝ) ≤ R ^ n := hRn.le
    have hCn0 : (0 : ℝ) ≤ (euclidVolConst / Real.sqrt (n : ℝ)) ^ n :=
      pow_nonneg (div_nonneg euclidVolConst_nonneg (Real.sqrt_nonneg _)) n
    calc R ^ n * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))
        = (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) * R ^ n :=
          mul_comm _ _
      _ ≤ (euclidVolConst / Real.sqrt (n : ℝ)) ^ n * R ^ n :=
          mul_le_mul hmain (le_refl _) hRn0 hCn0

/-! ### Volume bounds -/

/-- ENNReal packaging of the core inequality. -/
theorem core_volume_ineq_ofReal (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 ≤ R) :
    ENNReal.ofReal R ^ n
        * ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))
      ≤ ENNReal.ofReal ((euclidVolConst * R / Real.sqrt (n : ℝ)) ^ n) := by
  have hRn0 : (0 : ℝ) ≤ R ^ n := pow_nonneg hR n
  rw [← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul hRn0]
  apply ENNReal.ofReal_le_ofReal
  exact core_volume_ineq n hn R hR

/-- Volume of the Euclidean `R`-ball in `R^n` is at most `(CR/√n)^n`
(paper.tex l992-997). -/
theorem volume_euclidBall_le (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 ≤ R) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
      ≤ ENNReal.ofReal ((euclidVolConst * R / Real.sqrt (n : ℝ)) ^ n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  exact core_volume_ineq_ofReal n hn R hR

/-- Closed-ball version of the volume bound. -/
theorem volume_euclidClosedBall_le (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 ≤ R) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
      ≤ ENNReal.ofReal ((euclidVolConst * R / Real.sqrt (n : ℝ)) ^ n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin]
  exact core_volume_ineq_ofReal n hn R hR

/-! ### Packing bound -/

/-- Volumetric packing bound (paper.tex l1308-1324): an `r`-separated subset of
the `R`-ball has at most `(1 + 2R/r)^n` points. -/
theorem packing_card_le (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin n)))
    (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r)
    (hS : ∀ x ∈ S, dist x 0 ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → r ≤ dist x y) :
    (S.card : ℝ) ≤ (1 + 2 * R / r) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : S.card ≤ 1 :=
      Finset.card_le_one.mpr (fun a _ b _ => Subsingleton.elim a b)
    have hcast : (S.card : ℝ) ≤ 1 := by exact_mod_cast h1
    rw [pow_zero]
    exact hcast
  · have hn' : 0 < n := hn
    haveI : Nonempty (Fin n) := ⟨⟨0, hn'⟩⟩
    have hr2 : (0 : ℝ) < r / 2 := by linarith
    have hRr2 : (0 : ℝ) < R + r / 2 := by linarith [hR]
    have hdisj : Set.PairwiseDisjoint (↑S : Set (EuclideanSpace ℝ (Fin n)))
        (fun x => Metric.ball x (r / 2)) := by
      intro x hx y hy hxy
      show Disjoint (Metric.ball x (r / 2)) (Metric.ball y (r / 2))
      rw [Set.disjoint_left]
      intro z hzx hzy
      have hxS : x ∈ S := Finset.mem_coe.mp hx
      have hyS : y ∈ S := Finset.mem_coe.mp hy
      have hsep' := hsep x hxS y hyS hxy
      have h1 : dist z x < r / 2 := Metric.mem_ball.mp hzx
      have h2 : dist z y < r / 2 := Metric.mem_ball.mp hzy
      have htri := dist_triangle x z y
      rw [dist_comm x z] at htri
      linarith
    have hmeas : ∀ b ∈ S, MeasurableSet (Metric.ball b (r / 2)) :=
      fun b _ => measurableSet_ball
    have hU : volume (⋃ b ∈ S, Metric.ball b (r / 2))
        = ∑ p ∈ S, volume (Metric.ball p (r / 2)) :=
      MeasureTheory.measure_biUnion_finset hdisj hmeas
    have htrans : ∀ p ∈ S,
        volume (Metric.ball p (r / 2))
          = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2)) := by
      intro p _
      rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
    have hsum : (∑ p ∈ S, volume (Metric.ball p (r / 2)))
        = S.card
          • volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2)) := by
      calc (∑ p ∈ S, volume (Metric.ball p (r / 2)))
          = ∑ p ∈ S,
              volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2)) :=
            Finset.sum_congr rfl (fun p hp => htrans p hp)
        _ = S.card
            • volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2)) :=
            Finset.sum_const _
    have hsub : (⋃ b ∈ S, Metric.ball b (r / 2))
        ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + r / 2) := by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨x, hxS, hzx⟩ := hz
      have h1 : dist z x < r / 2 := Metric.mem_ball.mp hzx
      have h2 : dist x 0 ≤ R := hS x hxS
      have htri := dist_triangle z x 0
      have hmem : dist z 0 < R + r / 2 := by linarith
      exact Metric.mem_ball.mpr hmem
    have hle : S.card
          • volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2))
        ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + r / 2)) := by
      rw [← hsum, ← hU]
      exact MeasureTheory.measure_mono hsub
    have hKr : (0 : ℝ)
        < Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) :=
      div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) n)
        (Real.Gamma_pos_of_pos (by
          have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn'
          linarith))
    have ha : (0 : ℝ) < (r / 2) ^ n := pow_pos hr2 n
    have hb : (0 : ℝ) < (R + r / 2) ^ n := pow_pos hRr2 n
    have hcard : (S.card : ℝ)
          * (((r / 2) ^ n)
            * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)))
        ≤ ((R + r / 2) ^ n)
          * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) := by
      have e1 : ENNReal.ofReal (r / 2) ^ n = ENNReal.ofReal ((r / 2) ^ n) :=
        (ENNReal.ofReal_pow hr2.le n).symm
      have e2 : ENNReal.ofReal (R + r / 2) ^ n
          = ENNReal.ofReal ((R + r / 2) ^ n) :=
        (ENNReal.ofReal_pow hRr2.le n).symm
      rw [nsmul_eq_mul, EuclideanSpace.volume_ball, EuclideanSpace.volume_ball,
        Fintype.card_fin, e1, e2, ← ENNReal.ofReal_mul ha.le,
        ← ENNReal.ofReal_mul hb.le, ← ENNReal.ofReal_natCast] at hle
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hle
      have hBK0 : (0 : ℝ)
          ≤ ((R + r / 2) ^ n)
            * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) :=
        mul_nonneg hb.le hKr.le
      exact (ENNReal.ofReal_le_ofReal_iff hBK0).mp hle
    have h1 : (S.card : ℝ) * ((r / 2) ^ n) ≤ ((R + r / 2) ^ n) := by
      have hcard' : ((S.card : ℝ) * ((r / 2) ^ n))
            * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))
          ≤ ((R + r / 2) ^ n)
            * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) := by
        rw [mul_assoc]
        exact hcard
      exact le_of_mul_le_mul_right hcard' hKr
    have hdiv : (S.card : ℝ) ≤ ((R + r / 2) ^ n) / ((r / 2) ^ n) :=
      (le_div_iff₀ ha).mpr h1
    have hfin : ((R + r / 2) ^ n) / ((r / 2) ^ n) = (1 + 2 * R / r) ^ n := by
      rw [← div_pow]
      congr 1
      have hrne : r ≠ 0 := ne_of_gt hr
      have hr2ne : r / 2 ≠ 0 := ne_of_gt hr2
      field_simp
      ring
    rw [hfin] at hdiv
    exact hdiv

/-! ### Covering / net existence -/

/-- Volumetric covering bound (paper.tex l1308-1324): the `R`-ball admits a
finite internal `r`-net with at most `⌈(1 + 2R/r)^n⌉₊` centers. -/
theorem exists_net_closedBall (n : ℕ) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ c ∈ T, dist c 0 ≤ R) ∧
      (∀ x, dist x 0 ≤ R → ∃ c ∈ T, dist x c < r) ∧
      T.card ≤ Nat.ceil ((1 + 2 * R / r) ^ n) := by
  classical
  by_contra hyp
  have aux : ∀ j : ℕ, j ≤ Nat.ceil ((1 + 2 * R / r) ^ n) + 1 →
      ∃ S : Finset (EuclideanSpace ℝ (Fin n)),
        S.card = j ∧ (∀ x ∈ S, dist x 0 ≤ R) ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → r ≤ dist x y) := by
    intro j
    induction j with
    | zero =>
        intro _
        exact ⟨∅, Finset.card_empty, fun x hx => absurd hx (Finset.notMem_empty x),
          fun x hx => absurd hx (Finset.notMem_empty x)⟩
    | succ j ih =>
        intro hj1
        have hj : j ≤ Nat.ceil ((1 + 2 * R / r) ^ n) + 1 := by omega
        obtain ⟨S, hcard, hball, hsep⟩ := ih hj
        have hjK : j ≤ Nat.ceil ((1 + 2 * R / r) ^ n) := by omega
        have hcardK : S.card ≤ Nat.ceil ((1 + 2 * R / r) ^ n) := by omega
        have hnotnet : ¬ (∀ x, dist x 0 ≤ R → ∃ c ∈ S, dist x c < r) := by
          intro hnet
          exact hyp ⟨S, hball, hnet, hcardK⟩
        have hex : ∃ x, dist x 0 ≤ R ∧ ∀ c ∈ S, r ≤ dist x c := by
          by_contra hcon
          have hnn : ∀ x, dist x 0 ≤ R → ∃ c ∈ S, dist x c < r := by
            intro x hx
            by_contra hc
            push_neg at hc
            exact hcon ⟨x, hx, hc⟩
          exact hnotnet hnn
        obtain ⟨x, hxball, hxfar⟩ := hex
        have hxS : x ∉ S := by
          intro hxmem
          have h1 := hxfar x hxmem
          rw [dist_self] at h1
          linarith [hr]
        refine ⟨insert x S, ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hxS, hcard]
        · intro c hc
          rw [Finset.mem_insert] at hc
          rcases hc with rfl | hcS
          · exact hxball
          · exact hball c hcS
        · intro a ha b hb hne
          rw [Finset.mem_insert] at ha hb
          rcases ha with rfl | haS
          · rcases hb with rfl | hbS
            · exact False.elim (hne rfl)
            · exact hxfar b hbS
          · rcases hb with hbx | hbS
            · rw [hbx, dist_comm a x]
              exact hxfar a haS
            · exact hsep a haS b hbS hne
  obtain ⟨S, hcard, hball, hsep⟩ :=
    aux (Nat.ceil ((1 + 2 * R / r) ^ n) + 1) (le_refl _)
  have hpack := packing_card_le n S R r hR hr hball hsep
  rw [hcard] at hpack
  have hceil := Nat.le_ceil ((1 + 2 * R / r) ^ n)
  have hKK : ((Nat.ceil ((1 + 2 * R / r) ^ n) + 1 : ℕ) : ℝ)
      ≤ ((Nat.ceil ((1 + 2 * R / r) ^ n) : ℕ) : ℝ) :=
    le_trans hpack hceil
  have hcast : ((Nat.ceil ((1 + 2 * R / r) ^ n) + 1 : ℕ) : ℝ)
      = ((Nat.ceil ((1 + 2 * R / r) ^ n) : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast] at hKK
  linarith

/-! ### `euclidNorm` interface (via `NormBridges`) -/

/-- Distance in `EuclideanSpace` is `euclidNorm` of the difference. -/
theorem dist_toLp_eq_euclidNorm_sub {n : ℕ} (x y : Vector n) :
    dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 y) = euclidNorm (x - y) := by
  rw [dist_eq_norm, ← WithLp.toLp_sub, euclidNorm_eq_norm_toLp]

/-- Distance to the origin is `euclidNorm`. -/
theorem dist_toLp_zero_eq_euclidNorm {n : ℕ} (x : Vector n) :
    dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) 0 = euclidNorm x := by
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 (0 : Vector n) :=
    (WithLp.toLp_zero 2).symm
  rw [h0, dist_toLp_eq_euclidNorm_sub, sub_zero]

/-- Packing bound for `euclidNorm`-separated sets (paper.tex l1308-1324). -/
theorem packing_card_le_euclidNorm (n : ℕ) (S : Finset (Vector n))
    (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r)
    (hS : ∀ x ∈ S, euclidNorm x ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → r ≤ euclidNorm (x - y)) :
    (S.card : ℝ) ≤ (1 + 2 * R / r) ^ n := by
  let e : (Vector n) ↪ EuclideanSpace ℝ (Fin n) :=
    ⟨WithLp.toLp 2, WithLp.toLp_injective 2⟩
  have he : ∀ x, e x = (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) :=
    fun x => rfl
  have hcard : (S.map e).card = S.card := Finset.card_map e
  have hT := packing_card_le n (S.map e) R r hR hr
    (by
      intro c hc
      rw [Finset.mem_map] at hc
      obtain ⟨x, hxS, rfl⟩ := hc
      rw [he]
      rw [dist_toLp_zero_eq_euclidNorm]
      exact hS x hxS)
    (by
      intro a ha b hb hab
      rw [Finset.mem_map] at ha hb
      obtain ⟨x, hxS, rfl⟩ := ha
      obtain ⟨y, hyS, rfl⟩ := hb
      have hxy : x ≠ y := fun h => hab (congrArg e h)
      have h := hsep x hxS y hyS hxy
      rw [he, he]
      rw [dist_toLp_eq_euclidNorm_sub]
      exact h)
  rw [hcard] at hT
  exact hT

/-- Net existence for `euclidNorm` balls (paper.tex l1308-1324). -/
theorem exists_net_euclidNorm (n : ℕ) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ T : Finset (Vector n),
      (∀ c ∈ T, euclidNorm c ≤ R) ∧
      (∀ x, euclidNorm x ≤ R → ∃ c ∈ T, euclidNorm (x - c) < r) ∧
      T.card ≤ Nat.ceil ((1 + 2 * R / r) ^ n) := by
  obtain ⟨T, hball, hnet, hcard⟩ := exists_net_closedBall n R r hR hr
  let e' : (EuclideanSpace ℝ (Fin n)) ↪ (Vector n) :=
    ⟨WithLp.ofLp, WithLp.ofLp_injective 2⟩
  have he' : ∀ d, e' d = WithLp.ofLp d := fun d => rfl
  refine ⟨T.map e', ?_, ?_, ?_⟩
  · intro c hc
    rw [Finset.mem_map] at hc
    obtain ⟨d, hdT, rfl⟩ := hc
    rw [he']
    have h1 : euclidNorm (WithLp.ofLp d) = dist d 0 := by
      have h2 := dist_toLp_zero_eq_euclidNorm (WithLp.ofLp d)
      rw [WithLp.toLp_ofLp] at h2
      exact h2.symm
    rw [h1]
    exact hball d hdT
  · intro x hx
    have hxball : dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) 0 ≤ R := by
      rw [dist_toLp_zero_eq_euclidNorm]
      exact hx
    obtain ⟨d, hdT, hdist⟩ := hnet _ hxball
    refine ⟨e' d, Finset.mem_map.mpr ⟨d, hdT, rfl⟩, ?_⟩
    rw [he']
    have h1 : euclidNorm (x - WithLp.ofLp d)
        = dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) d := by
      have h2 := dist_toLp_eq_euclidNorm_sub x (WithLp.ofLp d)
      rw [WithLp.toLp_ofLp] at h2
      exact h2.symm
    rw [h1]
    exact hdist
  · rw [Finset.card_map]
    exact hcard

#print axioms volume_euclidBall_le
#print axioms volume_euclidClosedBall_le
#print axioms packing_card_le
#print axioms exists_net_closedBall
#print axioms packing_card_le_euclidNorm
#print axioms exists_net_euclidNorm

end GaussianEllipsoid
