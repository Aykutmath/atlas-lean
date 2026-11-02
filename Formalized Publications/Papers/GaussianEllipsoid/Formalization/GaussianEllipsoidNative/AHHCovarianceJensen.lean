import AHHPolarProductLaw
import AHHGaussianModelBridge
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Haar-to-Gaussian Jensen for the actual product-projector covariance operator. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers AHHAlgebraBridges
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 800000
namespace AHHRadial

abbrev ProductSpace (h : ℕ) := EuclideanSpace ℂ (Fin h × Fin h)
abbrev Operator (h : ℕ) := ProductSpace h →L[ℂ] ProductSpace h

/-- Genuine rank-one operator of a product vector. -/
def productProjector (h : ℕ) (x y : CE h) : Operator h :=
  cMatrixCLM (projector (fun p : Fin h × Fin h => x p.1 * y p.2))

def gaussianCovariance (n h : ℕ) (z : Fin n → CE h × CE h) : Operator h :=
  ∑ i, productProjector h (z i).1 (z i).2

def unitCovariance (n h : ℕ) (d : Directions n h) : Operator h :=
  ∑ i, productProjector h (d i).1 (d i).2

def unitCovarianceNorm (n h : ℕ) (d : Directions n h) : ℝ := ‖unitCovariance n h d‖

theorem continuous_productProjector (h : ℕ) :
    Continuous (fun z : CE h × CE h => productProjector h z.1 z.2) := by
  have hm : Continuous (fun z : CE h × CE h =>
      projector (fun p : Fin h × Fin h => z.1 p.1 * z.2 p.2)) := by
    apply continuous_pi
    intro p
    apply continuous_pi
    intro q
    unfold projector
    fun_prop
  exact ((Matrix.toEuclideanCLM (n := Fin h × Fin h) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp hm

theorem productProjector_smul (h : ℕ) (a b : ℝ) (x y : CE h) :
    productProjector h (a • x) (b • y) = (a^2*b^2) • productProjector h x y := by
  have he : projector (fun p : Fin h × Fin h => (a • x) p.1 * (b • y) p.2) =
      (a^2*b^2) • projector (fun p : Fin h × Fin h => x p.1 * y p.2) := by
    ext p q
    simp [projector, Complex.real_smul, star_mul]
    ring
  unfold productProjector
  rw [he]
  exact LinearMapClass.map_smul_of_tower
    (Matrix.toEuclideanCLM (n := Fin h × Fin h) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv _ _

theorem gaussianCovariance_assemble (n h : ℕ)
    (p : (Fin n → Radius × Radius) × Directions n h) :
    gaussianCovariance n h (assembleSample n h p) =
      ∑ i, radialWeight p.1 i • productProjector h (p.2 i).1 (p.2 i).2 := by
  unfold gaussianCovariance assembleSample assemblePair
  simp only [productProjector_smul, radialWeight]

theorem continuous_direction_projector (n h : ℕ) (i : Fin n) :
    Continuous (fun d : Directions n h => productProjector h (d i).1 (d i).2) := by
  have hi : Continuous (fun d : Directions n h => d i) := continuous_apply i
  have h1 : Continuous (fun d : Directions n h => ((d i).1 : CE h)) :=
    continuous_subtype_val.comp (continuous_fst.comp hi)
  have h2 : Continuous (fun d : Directions n h => ((d i).2 : CE h)) :=
    continuous_subtype_val.comp (continuous_snd.comp hi)
  have hc := (continuous_productProjector h).comp (h1.prodMk h2)
  simpa only [Function.comp_def] using hc

theorem continuous_unitCovarianceNorm (n h : ℕ) : Continuous (unitCovarianceNorm n h) := by
  unfold unitCovarianceNorm unitCovariance
  exact (continuous_finset_sum _ (fun i _ => continuous_direction_projector n h i)).norm

theorem continuous_gaussianCovariance (n h : ℕ) : Continuous (gaussianCovariance n h) := by
  unfold gaussianCovariance
  apply continuous_finset_sum
  intro i hi
  exact (continuous_productProjector h).comp (continuous_apply i)

theorem direction_projector_integrable (n h : ℕ) (hh : 0 < h) (i : Fin n) :
    Integrable (fun d : Directions n h => productProjector h (d i).1 (d i).2)
      (directionsLaw n h) := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  letI := directionsLaw_probability n h hh
  letI : CompactSpace (UnitDirection h) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : CE h) 1)
  have hi : Continuous (fun d : Directions n h => d i) := continuous_apply i
  have h1 : Continuous (fun d : Directions n h => ((d i).1 : CE h)) :=
    continuous_subtype_val.comp (continuous_fst.comp hi)
  have h2 : Continuous (fun d : Directions n h => ((d i).2 : CE h)) :=
    continuous_subtype_val.comp (continuous_snd.comp hi)
  have hc := (continuous_productProjector h).comp (h1.prodMk h2)
  simpa only [IntegrableOn, Measure.restrict_univ, Function.comp_def] using
    hc.continuousOn.integrableOn_compact (μ := directionsLaw n h) isCompact_univ

/-- Expected operator norm under the actual iid Haar product-state law is
bounded by the actual normalized complex Gaussian expectation. All radial
laws, means, independence, and integrability are proved upstream. -/
theorem unitCovariance_expected_norm_le_gaussian (n h : ℕ) (hh : 0 < h) :
    (∫ d, unitCovarianceNorm n h d ∂directionsLaw n h) ≤
      ∫ z, ‖gaussianCovariance n h z‖ ∂gaussianPairsLaw n h := by
  letI := directionsLaw_probability n h hh
  have he := integrated_jensen (directionsLaw n h) n h hh
    (fun d i => productProjector h (d i).1 (d i).2)
    (direction_projector_integrable n h hh)
  have hc : Continuous (fun z => ‖gaussianCovariance n h z‖) := by
    unfold gaussianCovariance
    apply Continuous.norm
    apply continuous_finset_sum
    intro i hi
    exact (continuous_productProjector h).comp (continuous_apply i)
  have hm := integral_map (μ := (radiiLaw n h).prod (directionsLaw n h))
    (φ := assembleSample n h) (f := fun z => ‖gaussianCovariance n h z‖)
    (assembleSample_preserving n h hh).measurable.aemeasurable
    hc.aestronglyMeasurable
  rw [(assembleSample_preserving n h hh).map_eq] at hm
  rw [hm]
  simp_rw [gaussianCovariance_assemble]
  exact he

theorem unitCovarianceNorm_integrable (n h : ℕ) (hh : 0 < h) :
    Integrable (unitCovarianceNorm n h) (directionsLaw n h) :=
  (integrable_finset_sum _ (fun i _ => direction_projector_integrable n h hh i)).norm

theorem gaussianCovariance_integrable (n h : ℕ) (hh : 0 < h) :
    Integrable (gaussianCovariance n h) (gaussianPairsLaw n h) := by
  letI := radiiLaw_probability n h hh
  letI := directionsLaw_probability n h hh
  have hw : Integrable (fun p : (Fin n → Radius × Radius) × Directions n h =>
      ∑ i, radialWeight p.1 i • productProjector h (p.2 i).1 (p.2 i).2)
      ((radiiLaw n h).prod (directionsLaw n h)) :=
    integrable_finset_sum _ (fun i _ => (radialWeight_integrable n h hh i).smul_prod
      (direction_projector_integrable n h hh i))
  apply ((assembleSample_preserving n h hh).integrable_comp
    (continuous_gaussianCovariance n h).aestronglyMeasurable).mp
  simpa only [Function.comp_def, gaussianCovariance_assemble] using hw

@[simp] theorem unitCovarianceNorm_zero_samples (h : ℕ) (d : Directions 0 h) :
    unitCovarianceNorm 0 h d = 0 := by simp [unitCovarianceNorm, unitCovariance]

#print axioms unitCovariance_expected_norm_le_gaussian
#print axioms gaussianCovariance_integrable
end AHHRadial
