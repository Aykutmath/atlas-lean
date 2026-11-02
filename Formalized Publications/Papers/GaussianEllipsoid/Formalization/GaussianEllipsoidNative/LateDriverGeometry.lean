import GaussianBlockAmplification

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianBilinearTransport GaussianEllipsoid GaussianEllipsoid.SmallBall
open scoped ENNReal
namespace GaussianPairedBlocks

/-- An even block dimension at the late driver's effective support scale. -/
def lateBlockDim (s d : ℕ) : ℕ := 2 * (min s d / 32)

theorem lateBlock_geometry_ambient {s d h : ℕ} (hm : 64 ≤ min s d) (hdh : d ≤ 3*h) :
    0 < h ∧ 0 < lateBlockDim s d ∧
    16 * lateBlockDim s d ≤ min s d ∧
    min s d ≤ 32 * lateBlockDim s d ∧
    d ≤ 6 * ((h / lateBlockDim s d) * lateBlockDim s d) := by
  let m := min s d
  let r := lateBlockDim s d
  have hmdef : m = min s d := rfl
  have hrdef : r = 2*(m/32) := rfl
  have hmul := Nat.div_mul_le_self m 32
  have hrem := Nat.mod_lt m (by norm_num : 0 < 32)
  have hdiv := Nat.mod_add_div m 32
  have hrp : 0 < r := by omega
  have hrd : 16*r ≤ d := by omega
  have h2r : 2*r ≤ h := by omega
  have hj : 1 ≤ h/r := (Nat.le_div_iff_mul_le hrp).mpr (by simpa using h2r.trans' (by omega : r ≤ 2*r))
  have hjmul : r ≤ (h/r)*r := by nlinarith
  have hremh := Nat.mod_lt (h) hrp
  have hdivh := Nat.mod_add_div (h) r
  have hhprod : h ≤ 2*((h/r)*r) := by nlinarith
  change 0 < h ∧ 0 < r ∧ 16*r ≤ min s d ∧ min s d ≤ 32*r ∧ d ≤ 6*((h/r)*r)
  constructor
  · omega
  constructor
  · exact hrp
  constructor
  · omega
  constructor
  · omega
  · omega

/-- The majority-block exponent has the macroscopic late-driver scale. -/
theorem lateBlock_exponent_ambient {s d h : ℕ} (hm : 64 ≤ min s d) (hdh : d ≤ 3*h) :
    (d:ℝ) * (min s d:ℕ) / 1024 ≤
      ((h / lateBlockDim s d : ℕ):ℝ) * (lateBlockDim s d:ℝ)^2 / 4 := by
  obtain ⟨hh,hr,hu,hl,hJ⟩ := lateBlock_geometry_ambient hm hdh
  have hJ' : (d:ℝ) ≤ 6 * (((h / lateBlockDim s d : ℕ):ℝ) * (lateBlockDim s d:ℝ)) := by
    exact_mod_cast hJ
  have hl' : (min s d:ℕ) ≤ (32:ℝ)*(lateBlockDim s d:ℝ) := by exact_mod_cast hl
  have hr' : (0:ℝ) ≤ lateBlockDim s d := by positivity
  have hd' : (0:ℝ) ≤ d := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hl' hd'
  have h₂ := mul_le_mul_of_nonneg_right hJ' hr'
  nlinarith

/-- A simple square-root comparison used to express the block threshold in l1 scale. -/
theorem late_mass_sqrt_comparison {s m r : ℕ} {M σ : ℝ}
    (hs : 0 < s) (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hMass : M^2 ≤ (s:ℝ)*σ^2) (hmr : m ≤ 32*r) :
    M * Real.sqrt ((m:ℝ)/s) ≤ 8*σ*Real.sqrt (r:ℝ) := by
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hroot := Real.sq_sqrt (show (0:ℝ) ≤ (m:ℝ)/s by positivity)
  have hrootr := Real.sq_sqrt (show (0:ℝ) ≤ r by positivity)
  have h₁ := mul_le_mul_of_nonneg_right hMass (show (0:ℝ) ≤ (m:ℝ)/s by positivity)
  have hcancel : ((s:ℝ)*σ^2)*((m:ℝ)/s) = σ^2*m := by field_simp
  rw [hcancel] at h₁
  have hmrR : (m:ℝ) ≤ 32*(r:ℝ) := by exact_mod_cast hmr
  have h₂ := mul_le_mul_of_nonneg_left hmrR (sq_nonneg σ)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (M * Real.sqrt ((m:ℝ)/s))^2 = M^2 * ((m:ℝ)/s) := by rw [mul_pow, hroot]
    _ ≤ σ^2*m := h₁
    _ ≤ 32*σ^2*r := by nlinarith
    _ ≤ (8*σ*Real.sqrt (r:ℝ))^2 := by rw [mul_pow, mul_pow, hrootr]; nlinarith [mul_nonneg (sq_nonneg σ) (show (0:ℝ) ≤ r by positivity)]

/-- Explicit l1 late-driver threshold, with a deliberately conservative dyadic constant. -/
theorem lateBlock_threshold_ambient {s d h : ℕ} (hm : 64 ≤ min s d) (hdh : d ≤ 3*h) {M σ : ℝ}
    (hM : 0 ≤ M) (hσ : 0 < σ) (hMass : M^2 ≤ (s:ℝ)*σ^2) :
    (1/1048576:ℝ) * Real.sqrt d * M * Real.sqrt ((min s d:ℕ)/ (s:ℝ)) ≤
      ((h / lateBlockDim s d : ℕ):ℝ)/2 * blockThreshold σ d (lateBlockDim s d) := by
  obtain ⟨hh,hr,hu,hl,hJ⟩ := lateBlock_geometry_ambient hm hdh
  have hs : 0 < s := by omega
  have hd : (0:ℝ) < d := by exact_mod_cast (show 0<d by omega)
  have hsd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hd
  have hsd2 := Real.sq_sqrt hd.le
  have hmass := late_mass_sqrt_comparison hs hM hσ.le hMass hl
  have hJ' : (d:ℝ) ≤ 6 * (((h / lateBlockDim s d : ℕ):ℝ) * (lateBlockDim s d:ℝ)) := by exact_mod_cast hJ
  have hpos : 0 ≤ σ * Real.sqrt (lateBlockDim s d:ℝ) := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hmass (show (0:ℝ) ≤ d by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hJ' hpos
  unfold blockThreshold
  rw [← mul_div_assoc, le_div_iff₀ (show 0 < 1024 * Real.sqrt (d:ℝ) by positivity)]
  calc
    _ = (1024/1048576:ℝ)*(d:ℝ)*(M * Real.sqrt ((min s d:ℕ)/(s:ℝ))) := by nlinarith [hsd2]
    _ ≤ (1024/1048576:ℝ)*(d:ℝ)*(8*σ*Real.sqrt (lateBlockDim s d:ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ ((h / lateBlockDim s d : ℕ):ℝ)/2 * (σ * (lateBlockDim s d:ℝ) * Real.sqrt (lateBlockDim s d:ℝ)) := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (h / lateBlockDim s d:ℕ) by positivity) hpos]

/-- Half-dimension convenience forms. -/
theorem lateBlock_geometry {s d : ℕ} (hm : 64 ≤ min s d) :
    0 < d/2 ∧ 0 < lateBlockDim s d ∧
    16 * lateBlockDim s d ≤ min s d ∧
    min s d ≤ 32 * lateBlockDim s d ∧
    d ≤ 6 * ((d/2 / lateBlockDim s d) * lateBlockDim s d) :=
  lateBlock_geometry_ambient hm (by omega)

theorem lateBlock_exponent {s d : ℕ} (hm : 64 ≤ min s d) :
    (d:ℝ) * (min s d:ℕ) / 1024 ≤
      ((d/2 / lateBlockDim s d : ℕ):ℝ) * (lateBlockDim s d:ℝ)^2 / 4 :=
  lateBlock_exponent_ambient hm (by omega)

theorem lateBlock_threshold {s d : ℕ} (hm : 64 ≤ min s d) {M σ : ℝ}
    (hM : 0 ≤ M) (hσ : 0 < σ) (hMass : M^2 ≤ (s:ℝ)*σ^2) :
    (1/1048576:ℝ) * Real.sqrt d * M * Real.sqrt ((min s d:ℕ)/ (s:ℝ)) ≤
      ((d/2 / lateBlockDim s d : ℕ):ℝ)/2 * blockThreshold σ d (lateBlockDim s d) :=
  lateBlock_threshold_ambient hm (by omega) hM hσ hMass

end GaussianPairedBlocks
