import GaussianTensorCovarianceTail
import FrobeniusCovarianceSynthesis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! The actual Euclidean-to-Frobenius bilinear Gaussian map has a fixed
constant high-probability operator norm bound, with explicit error probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorTrace GaussianEllipsoid Filter
open scoped BigOperators Topology

namespace GaussianTensorMoments

/-- The exact matrix-valued Gaussian bilinear operator B, including d^(-1/2). -/
def gaussianBilinearOperator (n h d : ℕ)
    (z : GaussianEntries n h × GaussianEntries n h) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] FrobeniusMatrix h h :=
  tensorFrobeniusSynthesis (fun i r => z.1 (i,r)) (fun i r => z.2 (i,r)) d

/-- Coordinates match d^(-1/2) sum_i y_i a_i b_i^T exactly. -/
theorem gaussianBilinearOperator_apply (n h d : ℕ)
    (z : GaussianEntries n h × GaussianEntries n h)
    (y : EuclideanSpace ℝ (Fin n)) (r s : Fin h) :
    frobeniusToMatrix (gaussianBilinearOperator n h d z y) r s =
      (Real.sqrt d)⁻¹ * ∑ i, y i * (z.1 (i,r)*z.2 (i,s)) :=
  tensorFrobeniusSynthesis_apply _ _ _ _ _ _

/-- Spectral covariance identity for the precise Euclidean/Frobenius norms. -/
theorem gaussianBilinearOperator_norm_sq (n h d : ℕ)
    (z : GaussianEntries n h × GaussianEntries n h) :
    ‖gaussianBilinearOperator n h d z‖^2 =
      ‖matrixCLM (tensorGaussianCovariance n h z)‖ / d := by
  exact tensorFrobeniusSynthesis_norm_sq _ _ _ (Nat.cast_nonneg d)

/-- Quantitative continuity at the aspect bound needed for MixedNormBound.
The covariance enlargement can simply use q=d, avoiding ceiling/square-root
rounding arguments entirely. -/
theorem gaussianBilinearOperator_norm_tail (n h d : ℕ)
    (hd : 0 < d) (hh : 0 < h) (hhd : h ≤ d) (hn : n ≤ d^2) :
    (tensorGaussianLaw n h).real
      {z | 96*Real.sqrt d < ‖gaussianBilinearOperator n h d z‖} ≤
      (h:ℝ)^2/(2:ℝ)^h := by
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hhdR : (h:ℝ)≤d := by exact_mod_cast hhd
  have hsub : {z | 96*Real.sqrt d < ‖gaussianBilinearOperator n h d z‖} ⊆
      {z | 2048*(h+d : ℕ)^2 < ‖matrixCLM (tensorGaussianCovariance n h z)‖} := by
    intro z hz
    change 2048*(h+d : ℕ)^2 < ‖matrixCLM (tensorGaussianCovariance n h z)‖
    have hsq : (96*Real.sqrt (d:ℝ))^2 < ‖gaussianBilinearOperator n h d z‖^2 :=
      (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr hz
    have hsqrt := Real.sq_sqrt (le_of_lt hdR)
    have hpow : 9216*(d:ℝ) < ‖gaussianBilinearOperator n h d z‖^2 := by
      nlinarith
    have hid := gaussianBilinearOperator_norm_sq n h d z
    have hid' : (d:ℝ)*‖gaussianBilinearOperator n h d z‖^2 =
        ‖matrixCLM (tensorGaussianCovariance n h z)‖ := by
      have ht := (eq_div_iff (ne_of_gt hdR)).mp hid
      nlinarith
    have hstrong := mul_lt_mul_of_pos_left hpow hdR
    have hs : ((h:ℝ)+d)^2 ≤ (2*(d:ℝ))^2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    push_cast
    nlinarith [sq_pos_of_pos hdR]
  exact (measureReal_mono hsub).trans
    (tensorGaussianCovariance_norm_tail n d h (by omega) hh hn)

/-- The explicit exceptional probability tends to zero. -/
theorem tensor_covariance_error_tendsto_zero :
    Tendsto (fun h : ℕ => (h:ℝ)^2/(2:ℝ)^h) atTop (𝓝 0) :=
  tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)

/-- Uniform high-probability bilinear continuity for every sequence n(d)≤d²
eventually, with the fixed constant L=96 and h=floor(d/2). -/
theorem gaussianBilinearOperator_bad_probability_tendsto_zero (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, n d ≤ d^2) :
    Tendsto (fun d => (tensorGaussianLaw (n d) (d/2)).real
      {z | 96*Real.sqrt d < ‖gaussianBilinearOperator (n d) (d/2) d z‖})
      atTop (𝓝 0) := by
  have hupper := tensor_covariance_error_tendsto_zero.comp
    (Nat.tendsto_div_const_atTop (by norm_num : (2:ℕ)≠0))
  apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _ hupper
  filter_upwards [hn, eventually_ge_atTop 2] with d hnd hd
  exact gaussianBilinearOperator_norm_tail (n d) (d/2) d (by omega) (by omega)
    (Nat.div_le_self d 2) hnd

/-- The even-half convention used by the endpoint determinant modules has the
same continuity bound: h=2 floor(d/4) tends to infinity and never exceeds d. -/
theorem gaussianBilinearOperator_even_bad_probability_tendsto_zero (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, n d ≤ d^2) :
    Tendsto (fun d => (tensorGaussianLaw (n d) (2*(d/4))).real
      {z | 96*Real.sqrt d < ‖gaussianBilinearOperator (n d) (2*(d/4)) d z‖})
      atTop (𝓝 0) := by
  have hdim : Tendsto (fun d : ℕ => 2*(d/4)) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop (4*M)] with d hd
    omega
  have hupper := tensor_covariance_error_tendsto_zero.comp hdim
  apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _ hupper
  filter_upwards [hn, eventually_ge_atTop 4] with d hnd hd
  exact gaussianBilinearOperator_norm_tail (n d) (2*(d/4)) d (by omega) (by omega)
    (by omega) hnd

#print axioms gaussianBilinearOperator_even_bad_probability_tendsto_zero
#print axioms gaussianBilinearOperator_norm_sq
#print axioms gaussianBilinearOperator_norm_tail
#print axioms gaussianBilinearOperator_bad_probability_tendsto_zero

end GaussianTensorMoments
