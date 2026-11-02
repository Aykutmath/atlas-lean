import GaussianCovarianceRotation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Gaussian rotation averaging with bounded first derivatives. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set Filter
open GaussianTensorMoments BMSmoothQuadraticComposition GaussianCovarianceRotation
open scoped BigOperators BoundedContinuousFunction Topology

namespace AHHGaussianSemigroup
variable {d : ℕ}

def average (f : Raw d →ᵇ ℝ) (t : ℝ) (x : Raw d) : ℝ :=
  ∫ y, f (first t (x,y)) ∂γ d

theorem integrable_first (f : Raw d →ᵇ ℝ) (t : ℝ) (x : Raw d) :
    Integrable (fun y => f (first t (x,y))) (γ d) := by
  apply (integrable_const ‖f‖).mono'
  · apply Continuous.aestronglyMeasurable
    exact f.continuous.comp (by unfold first; fun_prop)
  · exact ae_of_all _ fun y => f.norm_coe_le_norm _

theorem continuous_average (f : Raw d →ᵇ ℝ) : Continuous (fun z : ℝ × Raw d => average f z.1 z.2) := by
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro z
    exact (integrable_first f z.1 z.2).aestronglyMeasurable
  · intro z
    exact ae_of_all _ fun y => f.norm_coe_le_norm _
  · exact integrable_const _
  · exact ae_of_all _ fun y => f.continuous.comp (by unfold first; fun_prop)

theorem average_norm_le (f : Raw d →ᵇ ℝ) (t : ℝ) (x : Raw d) :
    ‖average f t x‖ ≤ ‖f‖ := by
  calc
    _ ≤ ∫ y, ‖f (first t (x,y))‖ ∂γ d := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Raw d, ‖f‖ ∂γ d := integral_mono (integrable_first f t x).norm
      (integrable_const _) (fun y => f.norm_coe_le_norm _)
    _ = ‖f‖ := by simp

def averageBounded (f : Raw d →ᵇ ℝ) (t : ℝ) : Raw d →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (average f t)
    ((continuous_average f).comp (continuous_const.prodMk continuous_id)) ‖f‖
    (average_norm_le f t)

@[simp] theorem averageBounded_apply (f : Raw d →ᵇ ℝ) (t : ℝ) (x : Raw d) :
    averageBounded f t x = average f t x := rfl

theorem average_lower (f : Raw d →ᵇ ℝ) {c : ℝ} (hc : ∀ x, c ≤ f x)
    (t : ℝ) (x : Raw d) : c ≤ average f t x := by
  have h := integral_mono (integrable_const c) (integrable_first f t x)
    (fun y => hc (first t (x,y)))
  simpa only [integral_const, probReal_univ, one_smul] using! h

theorem average_zero (f : Raw d →ᵇ ℝ) (x : Raw d) : average f 0 x = f x := by
  simp [average, first]

theorem average_pi_div_two (f : Raw d →ᵇ ℝ) (x : Raw d) :
    average f (Real.pi/2) x = ∫ y, f y ∂γ d := by
  simp [average, first]

def averageDerivative (F : SmoothTest (Fin d)) (t : ℝ) (x y : Raw d) : Raw d →L[ℝ] ℝ :=
  ∑ i, (Real.cos t * F.gradient i (first t (x,y))) •
    (ContinuousLinearMap.proj i : Raw d →L[ℝ] ℝ)

theorem hasFDeriv_first_value (F : SmoothTest (Fin d)) (t : ℝ) (x y : Raw d) :
    HasFDerivAt (fun z => F.value (first t (z,y))) (averageDerivative F t x y) x := by
  have hf : HasFDerivAt (fun z : Raw d => first t (z,y))
      (Real.cos t • ContinuousLinearMap.id ℝ (Raw d)) x := by
    simpa only [first] using! ((hasFDerivAt_id x).const_smul (Real.cos t)).add_const (Real.sin t • y)
  have h := (F.hasFDeriv (first t (x,y))).comp x hf
  convert! h using 1
  ext v
  simp only [averageDerivative, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, Pi.smul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem averageDerivative_norm_le (F : SmoothTest (Fin d)) (t : ℝ) (x y : Raw d) :
    ‖averageDerivative F t x y‖ ≤ ∑ i, ‖F.gradient i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have hproj : ‖(ContinuousLinearMap.proj i : Raw d →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by simpa using norm_le_pi_norm z i)
  have hx : |F.gradient i (first t (x,y))| ≤ ‖F.gradient i‖ :=
    F.gradient i |>.norm_coe_le_norm _
  calc
    _ ≤ 1 * ‖F.gradient i‖ * 1 :=
      mul_le_mul (mul_le_mul (Real.abs_cos_le_one t) hx (abs_nonneg _) zero_le_one)
        hproj (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem hasFDeriv_average (F : SmoothTest (Fin d)) (t : ℝ) (x : Raw d) :
    HasFDerivAt (average F.value t)
      (∑ i, (Real.cos t * average (F.gradient i) t x) •
        (ContinuousLinearMap.proj i : Raw d →L[ℝ] ℝ)) x := by
  have hc (z : Raw d) : Continuous (averageDerivative F t z) := by
    unfold averageDerivative
    apply continuous_finset_sum
    intro i hi
    exact (continuous_const.mul ((F.gradient i).continuous.comp (by unfold first; fun_prop))).smul
      continuous_const
  have hi (z : Raw d) : Integrable (averageDerivative F t z) (γ d) :=
    (integrable_const (∑ i, ‖F.gradient i‖)).mono' (hc z).aestronglyMeasurable
      (ae_of_all _ fun y => averageDerivative_norm_le F t z y)
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y => F.value (first t (z,y))) (F' := averageDerivative F t)
    (bound := fun _ => ∑ i, ‖F.gradient i‖) (s := Set.univ) (x₀ := x)
    Filter.univ_mem (Eventually.of_forall fun z => (integrable_first F.value t z).aestronglyMeasurable)
    (integrable_first F.value t x) (hc x).aestronglyMeasurable
    (ae_of_all _ fun y z _ => averageDerivative_norm_le F t z y)
    (integrable_const _) (ae_of_all _ fun y z _ => hasFDeriv_first_value F t z y)
  convert! hd using 1
  ext v
  rw [ContinuousLinearMap.integral_apply (hi x)]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, averageDerivative]
  rw [integral_finset_sum _ (fun i _ => ((integrable_first (F.gradient i) t x).const_mul
    (Real.cos t)).mul_const (v i))]
  simp only [integral_mul_const, integral_const_mul, average]

def averageTest (F : SmoothTest (Fin d)) (t : ℝ) : SmoothTest (Fin d) where
  value := averageBounded F.value t
  gradient i := Real.cos t • averageBounded (F.gradient i) t
  hasFDeriv x := hasFDeriv_average F t x

#print axioms averageTest
end AHHGaussianSemigroup
