import GaussianBlockAmplification
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace GaussianEllipsoid.ProjectedClusters

def regularBlockHalf (R : ℝ) : ℕ := ⌊R / 2048⌋₊
def regularBlockSize (R : ℝ) : ℕ := 2 * regularBlockHalf R

/-- Even rounding retains half the nominal R/1024 block size. -/
theorem regularBlockSize_bounds {R : ℝ} (hR : 4096 ≤ R) :
    2 ≤ regularBlockSize R ∧ R / 2048 ≤ regularBlockSize R ∧
      (regularBlockSize R : ℝ) ≤ R / 1024 := by
  have hR0 : 0 ≤ R / 2048 := by linarith
  have hf := Nat.floor_le hR0
  have hg := Nat.lt_floor_add_one (R / 2048)
  have hh : 1 ≤ regularBlockHalf R := by
    dsimp [regularBlockHalf]
    apply Nat.le_floor
    norm_num
    linarith
  dsimp [regularBlockSize, regularBlockHalf] at *
  push_cast
  constructor
  · omega
  constructor <;> linarith

/-- Enough coordinate blocks fit in every residual rank at least d/4. -/
theorem regularBlockCount_bounds {R d : ℝ} {k : ℕ}
    (hR : 4096 ≤ R) (hRd : R ≤ d) (hk : d / 4 ≤ k) :
    let r := regularBlockSize R
    let J := k / r
    J * r ≤ k ∧ d ≤ 8 * (J : ℝ) * r := by
  dsimp
  have hr := regularBlockSize_bounds hR
  have hr0 : 0 < regularBlockSize R := by omega
  have hkrem := Nat.mod_lt k hr0
  have hdiv := Nat.mod_add_div k (regularBlockSize R)
  rw [Nat.mul_comm (regularBlockSize R) (k / regularBlockSize R)] at hdiv
  have hdivR : (k : ℝ) < ((k / regularBlockSize R : ℕ) : ℝ) * regularBlockSize R +
      regularBlockSize R := by exact_mod_cast (by omega : k < k / regularBlockSize R * regularBlockSize R + regularBlockSize R)
  constructor
  · exact Nat.div_mul_le_self _ _
  · have hsize : (regularBlockSize R : ℝ) ≤ d / 1024 := hr.2.2.trans (by linarith)
    nlinarith

/-- The explicit majority-block exponent gives the Section 7 dR scale. -/
theorem regularBlock_exponent {R d : ℝ} {k : ℕ}
    (hR : 4096 ≤ R) (hRd : R ≤ d) (hk : d / 4 ≤ k) :
    d * R / 65536 ≤
      ((k / regularBlockSize R : ℕ) : ℝ) * (regularBlockSize R : ℝ)^2 / 4 := by
  have hr := regularBlockSize_bounds hR
  have hc := (regularBlockCount_bounds hR hRd hk).2
  have hd : 0 ≤ d := by linarith
  have hmul := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (regularBlockSize R))
  have hmul2 := mul_le_mul_of_nonneg_left hr.2.1 hd
  nlinarith

/-- The regular coefficient cap implies the exact small-ball cap at the even block size. -/
theorem regularBlock_coefficient_cap {R σ x : ℝ} (hR : 4096 ≤ R) (hσ : 0 < σ)
    (hx : |x| ≤ 16 * σ / Real.sqrt R) :
    x^2 ≤ σ^2 * (2 * (regularBlockSize R : ℝ))⁻¹ := by
  have hR0 : 0 < R := by linarith
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
  have hx' : |x| * Real.sqrt R ≤ 16 * σ := (le_div_iff₀ hs).mp hx
  have hsq := (sq_le_sq₀ (mul_nonneg (abs_nonneg x) hs.le) (by positivity)).mpr hx'
  rw [mul_pow, sq_abs, Real.sq_sqrt hR0.le] at hsq
  have hr := regularBlockSize_bounds hR
  have hr0 : (0 : ℝ) < regularBlockSize R := by exact_mod_cast (by omega : 0 < regularBlockSize R)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 2 * (regularBlockSize R : ℝ))]
  have hh := mul_le_mul_of_nonneg_left hr.2.2 (sq_nonneg x)
  nlinarith [sq_nonneg σ]

/-- Conservative universal projected nuclear constant from ν=1/1024. -/
def projectedConstant : ℝ := 1 / (524288 * Real.sqrt 2)

theorem projectedConstant_pos : 0 < projectedConstant := by unfold projectedConstant; positivity

/-- The amplified block radius dominates the paper's √d·mass scale. -/
theorem regularBlock_threshold {R d σ m : ℝ} {k : ℕ}
    (hR : 4096 ≤ R) (hRd : R ≤ d) (hk : d / 4 ≤ k)
    (hσ : 0 < σ) (hm : m = σ * Real.sqrt R) :
    projectedConstant * Real.sqrt d * m ≤
      ((k / regularBlockSize R : ℕ) : ℝ) / 2 *
        GaussianPairedBlocks.blockThreshold σ d (regularBlockSize R) := by
  have hd : 0 < d := by linarith
  have hr := regularBlockSize_bounds hR
  have hc := (regularBlockCount_bounds hR hRd hk).2
  have hr0 : (0 : ℝ) ≤ regularBlockSize R := Nat.cast_nonneg _
  have hsR : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hsr : 0 ≤ Real.sqrt (regularBlockSize R : ℝ) := Real.sqrt_nonneg _
  have hs2 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsD : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hs : Real.sqrt R ≤ 32 * Real.sqrt 2 * Real.sqrt (regularBlockSize R : ℝ) := by
    apply (sq_le_sq₀ hsR (by positivity)).mp
    rw [Real.sq_sqrt (by linarith : 0 ≤ R)]
    nlinarith [Real.sq_sqrt hr0, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hc' := mul_le_mul_of_nonneg_right hc hsr
  have hc'' := mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ 32 * Real.sqrt 2)
  have hs' := mul_le_mul_of_nonneg_left hs hd.le
  have ht : d * Real.sqrt R ≤ 256 * Real.sqrt 2 *
      ((k / regularBlockSize R : ℕ) : ℝ) * regularBlockSize R *
      Real.sqrt (regularBlockSize R : ℝ) := by nlinarith
  unfold projectedConstant GaussianPairedBlocks.blockThreshold
  rw [hm]
  calc
    _ = (σ * Real.sqrt d * Real.sqrt R) / (524288 * Real.sqrt 2) := by ring
    _ ≤ (((k / regularBlockSize R : ℕ) : ℝ) * σ * regularBlockSize R *
        Real.sqrt (regularBlockSize R : ℝ)) / (2048 * Real.sqrt d) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hmul := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2048 * σ)
      convert hmul using 1 <;> ring_nf
      rw [Real.sq_sqrt hd.le]
      ring
    _ = _ := by ring

/-- The nuclear constant is below the independently proved exponent constant. -/
theorem projectedConstant_le_exponent : projectedConstant ≤ 1 / 65536 := by
  have hs : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  unfold projectedConstant
  apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 65536)
  nlinarith

/-- The paper's logarithmic lower cutoff implies the explicit absolute cutoff. -/
theorem regularCluster_log_cutoff {d : ℕ} {R : ℝ} (hd : 2 ≤ d)
    (hR : 8192 * Real.log d ≤ R) : 4096 ≤ R := by
  have hlog2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
  have hlogd := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by exact_mod_cast hd : (2:ℝ) ≤ d)
  norm_num at hlog2
  linarith

end GaussianEllipsoid.ProjectedClusters
