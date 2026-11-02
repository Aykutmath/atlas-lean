import AHHGaussianLogSobolev
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Intrinsic real-Hilbert and scaled forms of the proved Gaussian LSI. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set Filter
open GaussianTensorMoments BMSmoothQuadraticComposition GaussianCovarianceRotation
open AHHGaussianFisherContraction
open scoped BigOperators BoundedContinuousFunction Topology

namespace AHHGaussianIntrinsicLogSobolev
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {d : ℕ}

def coordinates (b : OrthonormalBasis (Fin d) ℝ E) : Raw d →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i : Raw d →L[ℝ] ℝ).smulRight (b i)

@[simp] theorem coordinates_apply (b : OrthonormalBasis (Fin d) ℝ E) (x : Raw d) :
    coordinates b x = ∑ i, x i • b i := by
  simp [coordinates]

theorem coordinates_preserving (b : OrthonormalBasis (Fin d) ℝ E) :
    MeasurePreserving (coordinates b) (γ d) (stdGaussian E) := by
  refine ⟨(coordinates b).continuous.measurable, ?_⟩
  change Measure.map (fun x => coordinates b x) (γ d) = stdGaussian E
  simp_rw [coordinates_apply]
  simpa only [GaussianTensorMoments.gaussianProductLaw] using
    (stdGaussian_eq_map_pi_orthonormalBasis b).symm

def intrinsicTest (b : OrthonormalBasis (Fin d) ℝ E) (f : E → ℝ)
    (hf : ContDiff ℝ 1 f) (B D : ℝ) (hB : ∀ x, ‖f x‖ ≤ B)
    (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) : SmoothTest (Fin d) where
  value := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f (coordinates b x))
    (hf.continuous.comp (coordinates b).continuous) B (fun x => hB _)
  gradient i := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => fderiv ℝ f (coordinates b x) (b i))
    (((hf.continuous_fderiv (by simp)).comp (coordinates b).continuous).clm_apply continuous_const)
    D (fun x => by
      have h := (fderiv ℝ f (coordinates b x)).le_opNorm (b i)
      simpa only [b.orthonormal.norm_eq_one i, mul_one] using h.trans
        (mul_le_mul_of_nonneg_right (hD _) (norm_nonneg (b i))))
  hasFDeriv x := by
    have h := ((hf.differentiable (by norm_num)) (coordinates b x)).hasFDerivAt.comp x
      (coordinates b).hasFDerivAt
    convert! h using 1
    ext v
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup, smul_eq_mul,
      coordinates_apply, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem intrinsicTest_energy (b : OrthonormalBasis (Fin d) ℝ E) (f : E → ℝ)
    (hf : ContDiff ℝ 1 f) (B D : ℝ) (hB : ∀ x, ‖f x‖ ≤ B)
    (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (x : Raw d) :
    (∑ i, ((intrinsicTest b f hf B D hB hD).gradient i x)^2) =
      ‖fderiv ℝ f (coordinates b x)‖^2 :=
  (b.norm_dual (fderiv ℝ f (coordinates b x))).symm

/-- The real derivative operator norm, rather than the raw-coordinate sup norm,
is exactly the squared Euclidean gradient in Gaussian LSI. -/
theorem stdGaussian_logSobolev (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    {c B D : ℝ} (hc : 0 < c) (hlo : ∀ x, c ≤ f x)
    (hB : ∀ x, ‖f x‖ ≤ B) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    (∫ x, f x * Real.log (f x) ∂stdGaussian E) -
      (∫ x, f x ∂stdGaussian E) * Real.log (∫ x, f x ∂stdGaussian E) ≤
      (1/2 : ℝ) * ∫ x, ‖fderiv ℝ f x‖^2 / f x ∂stdGaussian E := by
  let b := stdOrthonormalBasis ℝ E
  let F := intrinsicTest b f hf B D hB hD
  have h := AHHGaussianLogSobolev.gaussian_logSobolev F hc (fun x => hlo _)
  have hval : (∫ x, F.value x ∂γ (Module.finrank ℝ E)) = ∫ x, f x ∂stdGaussian E :=
    integral_preserving (coordinates_preserving b) hf.continuous.aestronglyMeasurable
  have hent : (∫ x, F.value x * Real.log (F.value x) ∂γ (Module.finrank ℝ E)) =
      ∫ x, f x * Real.log (f x) ∂stdGaussian E :=
    integral_preserving (coordinates_preserving b)
      (hf.continuous.measurable.mul hf.continuous.measurable.log).aestronglyMeasurable
  have henergy : (∫ x, (∑ i, (F.gradient i x)^2) / F.value x ∂γ (Module.finrank ℝ E)) =
      ∫ x, ‖fderiv ℝ f x‖^2 / f x ∂stdGaussian E := by
    simp only [F, intrinsicTest_energy]
    exact integral_preserving (coordinates_preserving b)
      (((hf.continuous_fderiv (by simp)).measurable.norm.pow_const 2).div
        hf.continuous.measurable).aestronglyMeasurable
  rwa [hval, hent, henergy] at h

/-- Scalar pushforward gives the exact Gaussian covariance factor. -/
theorem scaled_stdGaussian_logSobolev (s : ℝ) (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    {c B D : ℝ} (hc : 0 < c) (hlo : ∀ x, c ≤ f x)
    (hB : ∀ x, ‖f x‖ ≤ B) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    (∫ x, f x * Real.log (f x) ∂(stdGaussian E).map (fun x => s • x)) -
      (∫ x, f x ∂(stdGaussian E).map (fun x => s • x)) *
        Real.log (∫ x, f x ∂(stdGaussian E).map (fun x => s • x)) ≤
      (s^2/2) * ∫ x, ‖fderiv ℝ f x‖^2 / f x ∂(stdGaussian E).map (fun x => s • x) := by
  let g := fun x : E => f (s • x)
  have hg : ContDiff ℝ 1 g := hf.comp (contDiff_const.smul contDiff_id)
  have hder (x : E) : fderiv ℝ g x = s • fderiv ℝ f (s • x) := by
    have h := ((hf.differentiable (by norm_num)) (s • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul s)
    have he : (fderiv ℝ f (s • x)).comp (s • ContinuousLinearMap.id ℝ E) =
        s • fderiv ℝ f (s • x) := by
      ext v
      simp
    rw [he] at h
    exact h.fderiv
  have hgb (x : E) : ‖fderiv ℝ g x‖ ≤ |s| * D := by
    rw [hder, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
  have h := stdGaussian_logSobolev g hg hc (fun x => hlo _) (fun x => hB _) hgb
  have hm : Measurable (fun x : E => s • x) := by fun_prop
  have hmap (v : E → ℝ) (hv : AEStronglyMeasurable v ((stdGaussian E).map (fun x => s • x))) :
      (∫ x, v x ∂(stdGaussian E).map (fun x => s • x)) = ∫ x, v (s • x) ∂stdGaussian E :=
    integral_map hm.aemeasurable hv
  have hval := hmap f hf.continuous.aestronglyMeasurable
  have hent := hmap (fun x => f x * Real.log (f x))
    (hf.continuous.measurable.mul hf.continuous.measurable.log).aestronglyMeasurable
  have he := hmap (fun x => ‖fderiv ℝ f x‖^2 / f x)
    (((hf.continuous_fderiv (by simp)).measurable.norm.pow_const 2).div
      hf.continuous.measurable).aestronglyMeasurable
  have henergy : (∫ x, ‖fderiv ℝ g x‖^2 / g x ∂stdGaussian E) =
      s^2 * ∫ x, ‖fderiv ℝ f x‖^2 / f x ∂(stdGaussian E).map (fun x => s • x) := by
    simp_rw [hder, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_div_assoc]
    rw [integral_const_mul, he]
  rw [henergy] at h
  rw [hval, hent]
  dsimp only [g] at h
  linarith

#print axioms scaled_stdGaussian_logSobolev
#print axioms stdGaussian_logSobolev
end AHHGaussianIntrinsicLogSobolev
