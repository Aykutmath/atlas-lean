import GaussianRotation
import BMGaussianEnergy
set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers BMGeometry
open scoped BigOperators InnerProductSpace
namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

instance euclideanGaussian_probability : IsProbabilityMeasure (euclideanGaussianLaw ι) := by
  unfold euclideanGaussianLaw
  exact Measure.isProbabilityMeasure_map (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.aemeasurable

theorem gaussian_linear_sq_integrable (a : ι → ℝ) :
    Integrable (fun x : ι → ℝ => (∑ i, a i * x i)^2) (gaussianProductLaw ι) := by
  have heq (x : ι → ℝ) : (∑ i, a i * x i)^2 =
      ∑ i, ∑ j, (a i*a j) * (x i*x j) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [heq]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (gaussian_coordinate_mul_integrable i j).const_mul _

theorem gaussian_linear_sq_moment (a : ι → ℝ) :
    (∫ x : ι → ℝ, (∑ i, a i * x i)^2 ∂gaussianProductLaw ι) = ∑ i, (a i)^2 := by
  classical
  have heq (x : ι → ℝ) : (∑ i, a i * x i)^2 =
      ∑ i, ∑ j, (a i*a j) * (x i*x j) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [heq]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
    (gaussian_coordinate_mul_integrable i j).const_mul _)]
  simp_rw [integral_finset_sum _ (fun j _ =>
    (gaussian_coordinate_mul_integrable _ j).const_mul _), integral_const_mul,
    gaussian_coordinate_covariance]
  simp [← pow_two]

theorem euclidean_integrable_inner_sq (a : E ι) :
    Integrable (fun x : E ι => ⟪a,x⟫_ℝ^2) (euclideanGaussianLaw ι) := by
  have h := gaussian_linear_sq_integrable (fun i => a i)
  have ht := (BMQuadraticSpectral.coordinates_preserving (ι := ι)).integrable_comp
    (g := fun x : ι → ℝ => (∑ i, a i*x i)^2)
    ((by fun_prop : Continuous (fun x : ι → ℝ => (∑ i, a i*x i)^2)).aestronglyMeasurable)
  apply ht.mpr at h
  convert h using 1
  funext x
  congr 1
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem euclidean_integral_inner_sq (a : E ι) :
    (∫ x : E ι, ⟪a,x⟫_ℝ^2 ∂euclideanGaussianLaw ι) = ‖a‖^2 := by
  have h := (BMQuadraticSpectral.coordinates_preserving (ι := ι)).integral_comp
    ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).measurableEmbedding
    (fun x : ι → ℝ => (∑ i, a i*x i)^2)
  rw [gaussian_linear_sq_moment] at h
  convert h using 1
  · congr 1; funext x; congr 1
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
    apply Finset.sum_congr rfl; intro i hi; exact mul_comm _ _
  · simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

theorem euclidean_integrable_linear_sq (L : E ι →L[ℝ] ℝ) :
    Integrable (fun x : E ι => (L x)^2) (euclideanGaussianLaw ι) := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    euclidean_integrable_inner_sq ((InnerProductSpace.toDual ℝ (E ι)).symm L)

theorem euclidean_integral_linear_sq (L : E ι →L[ℝ] ℝ) :
    (∫ x : E ι, (L x)^2 ∂euclideanGaussianLaw ι) = ‖L‖^2 := by
  simpa only [InnerProductSpace.toDual_symm_apply,
    LinearIsometryEquiv.norm_map] using
    euclidean_integral_inner_sq ((InnerProductSpace.toDual ℝ (E ι)).symm L)

end GaussianVariance

namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

theorem euclidean_integrable_norm_sq :
    Integrable (fun x : E ι => ‖x‖^2) (euclideanGaussianLaw ι) := by
  have h : Integrable (fun x : ι → ℝ => ∑ i, (x i)^2) (gaussianProductLaw ι) :=
    integrable_finset_sum _ fun i _ => gaussian_coordinate_integrable_pow i 2
  have ht := (BMQuadraticSpectral.coordinates_preserving (ι := ι)).integrable_comp
    (g := fun x : ι → ℝ => ∑ i, (x i)^2)
    ((by fun_prop : Continuous (fun x : ι → ℝ => ∑ i, (x i)^2)).aestronglyMeasurable)
  apply ht.mpr at h
  simpa only [Function.comp_def, MeasurableEquiv.coe_toLp_symm, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using h

theorem euclidean_integrable_norm :
    Integrable (fun x : E ι => ‖x‖) (euclideanGaussianLaw ι) := by
  exact ((memLp_two_iff_integrable_sq (μ := euclideanGaussianLaw ι)
    (f := fun x : E ι => ‖x‖) continuous_norm.aestronglyMeasurable).mpr
      (euclidean_integrable_norm_sq (ι := ι))).integrable (by norm_num)

theorem pair_norm_fst_sq_integrable :
    Integrable (fun z : E ι × E ι => ‖z.1‖^2)
      ((euclideanGaussianLaw ι).prod (euclideanGaussianLaw ι)) := by
  simpa only [mul_one] using (euclidean_integrable_norm_sq (ι := ι)).mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : E ι => (1 : ℝ)) (euclideanGaussianLaw ι))

theorem pair_norm_snd_sq_integrable :
    Integrable (fun z : E ι × E ι => ‖z.2‖^2)
      ((euclideanGaussianLaw ι).prod (euclideanGaussianLaw ι)) := by
  simpa only [one_mul] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : E ι => (1 : ℝ)) (euclideanGaussianLaw ι)).mul_prod
    (euclidean_integrable_norm_sq (ι := ι))

theorem pair_energy_integrable :
    Integrable (fun z : E ι × E ι => 2*(‖z.1‖^2+‖z.2‖^2))
      ((euclideanGaussianLaw ι).prod (euclideanGaussianLaw ι)) :=
  (pair_norm_fst_sq_integrable.add pair_norm_snd_sq_integrable).const_mul 2

end GaussianVariance
