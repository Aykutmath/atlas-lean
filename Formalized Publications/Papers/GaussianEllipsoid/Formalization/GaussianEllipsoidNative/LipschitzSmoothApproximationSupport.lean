/- NEW SUPPORT MODULE, 2026-10-03. Not recovered original source bytes.
   Positive normalized convolution preserves the exact Lipschitz constant. -/
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open MeasureTheory ContinuousLinearMap Metric Set
open scoped Convolution ContDiff Topology

namespace LipschitzSmoothApproximationSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

def smooth (φ : ContDiffBump (0 : E)) (f : E → ℝ) : E → ℝ :=
  φ.normed μ ⋆[lsmul ℝ ℝ, μ] f

theorem smooth_contDiff (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : Continuous f) : ContDiff ℝ ∞ (smooth (μ := μ) φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf.locallyIntegrable

theorem smooth_integrable (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : Continuous f) (x : E) :
    Integrable (fun t => φ.normed μ t * f (x - t)) μ := by
  exact φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
    φ.continuous_normed hf.locallyIntegrable x

theorem smooth_nonneg (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ∀ x, 0 ≤ f x) (x : E) : 0 ≤ smooth (μ := μ) φ f x := by
  exact integral_nonneg (fun t => mul_nonneg (φ.nonneg_normed t) (hf (x - t)))

theorem smooth_le (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, f x ≤ C) (x : E) :
    smooth (μ := μ) φ f x ≤ C := by
  have h := integral_mono (smooth_integrable (μ := μ) φ hf x) ((φ.integrable_normed (μ := μ)).mul_const C)
    (fun t => mul_le_mul_of_nonneg_left (hC (x - t)) (φ.nonneg_normed t))
  simpa [smooth, convolution, integral_mul_const, φ.integral_normed] using h

theorem smooth_lipschitz (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : LipschitzWith 1 f) : LipschitzWith 1 (smooth (μ := μ) φ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have heq : smooth (μ := μ) φ f x - smooth (μ := μ) φ f y =
      ∫ t, φ.normed μ t * (f (x - t) - f (y - t)) ∂μ := by
    simp only [smooth, convolution, lsmul_apply, smul_eq_mul]
    rw [← integral_sub (smooth_integrable φ hf.continuous x)
      (smooth_integrable φ hf.continuous y)]
    congr 1
    funext t
    ring
  rw [dist_eq_norm, heq]
  have h := norm_integral_le_of_norm_le (φ.integrable_normed.mul_const (dist x y))
    (Filter.Eventually.of_forall (fun t => show
      ‖φ.normed μ t * (f (x - t) - f (y - t))‖ ≤ φ.normed μ t * dist x y from by
        rw [norm_mul, Real.norm_of_nonneg (φ.nonneg_normed t), ← dist_eq_norm]
        apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
        simpa using hf.dist_le_mul (x - t) (y - t)))
  simpa [integral_mul_const, φ.integral_normed] using h

theorem smooth_dist_le (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : LipschitzWith 1 f) (x : E) :
    dist (smooth (μ := μ) φ f x) (f x) ≤ φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  have h : dist (f y) (f x) ≤ dist y x := by simpa using hf.dist_le_mul y x
  exact h.trans (mem_ball.mp hy).le

include μ in
/-- Positive smooth approximation, retaining the sharp Lipschitz constant and bounds. -/
theorem exists_smooth_bounded {f : E → ℝ} (hf : LipschitzWith 1 f)
    (hpos : ∀ x, 0 ≤ f x) {C ε : ℝ} (hC : ∀ x, f x ≤ C) (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith 1 g ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ C) ∧ (∀ x, dist (g x) (f x) ≤ ε) := by
  let φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  exact ⟨smooth (μ := μ) φ f, smooth_contDiff φ hf.continuous,
    smooth_lipschitz φ hf, smooth_nonneg φ hpos, smooth_le φ hf.continuous hC,
    smooth_dist_le φ hf⟩

include μ in
/-- Every nonnegative 1-Lipschitz function has nonnegative bounded smooth approximants.
    The envelope is independent of the approximation index. This includes dimension zero. -/
theorem exists_smooth_sequence {f : E → ℝ} (hf : LipschitzWith 1 f)
    (hpos : ∀ x, 0 ≤ f x) :
    ∃ g : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, LipschitzWith 1 (g n)) ∧
      (∀ n x, 0 ≤ g n x) ∧ (∀ n x, g n x ≤ (n : ℝ)) ∧
      (∀ n x, g n x ≤ f x + 1) ∧
      (∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop (𝓝 (f x))) := by
  have heps (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have happ (n : ℕ) := exists_smooth_bounded (μ := μ) (hf.min_const (n : ℝ))
    (fun x => le_min (hpos x) (Nat.cast_nonneg n)) (fun x => min_le_right (f x) (n : ℝ))
    (heps n)
  choose g hdiff hlip hnonneg hbound herr using happ
  refine ⟨g, hdiff, hlip, hnonneg, hbound, ?_, ?_⟩
  · intro n x
    have he := herr n x
    rw [Real.dist_eq] at he
    have hrad : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have := (abs_le.mp he).2
    have := min_le_left (f x) (n : ℝ)
    linarith
  · intro x
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
    have hlarge : ∀ᶠ n : ℕ in Filter.atTop, f x ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (f x))
    filter_upwards [hsmall, hlarge] with n hn hn'
    have he := herr n x
    rw [min_eq_left hn'] at he
    exact he.trans_lt hn

end LipschitzSmoothApproximationSupport

#print axioms LipschitzSmoothApproximationSupport.smooth_lipschitz
#print axioms LipschitzSmoothApproximationSupport.exists_smooth_bounded
#print axioms LipschitzSmoothApproximationSupport.exists_smooth_sequence
