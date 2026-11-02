import GaussianLinearSmallBall

noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Module
open GaussianMixedNormHelpers GaussianTensorMoments
open scoped ENNReal

namespace GaussianEllipsoid.SmallBall
variable {ι : Type*} [Fintype ι]

/-- Extended inverse Jacobian, retaining infinity on singular linear maps. -/
def inverseJacobian (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  (ENNReal.ofReal |LinearMap.det T|)⁻¹

/-- With a positive radius, singular maps can be included without an extra
hypothesis by using the correct extended inverse determinant. -/
theorem euclideanGaussian_linear_closedBall_le_extended {k : ℕ}
    (hcard : Fintype.card ι = 2 * k) (hk : 0 < k)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι)
    {R : ℝ} (hR : 0 < R) :
    euclideanGaussianLaw ι (T ⁻¹' closedBall c R) ≤
      inverseJacobian T *
        ENNReal.ofReal ((R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) := by
  by_cases hT : LinearMap.det T = 0
  · have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hC : ENNReal.ofReal ((R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) ≠ 0 := by
      apply ENNReal.ofReal_ne_zero_iff.mpr
      positivity
    simp only [inverseJacobian, hT, abs_zero, ENNReal.ofReal_zero, ENNReal.inv_zero,
      ENNReal.top_mul hC]
    exact le_top
  · have hj : ENNReal.ofReal |(LinearMap.det T)⁻¹| = inverseJacobian T := by
      rw [abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hT)]
      rfl
    rw [← hj]
    exact euclideanGaussian_linear_closedBall_le hcard hk T hT c (le_of_lt hR)

/-- Fubini integrates arbitrary independent random centers and linear maps.
The only measurability premise is for the actual displayed joint map. No
conditional-distribution axiom or assumed small-ball property appears. -/
theorem joint_euclideanGaussian_linear_closedBall_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {k : ℕ} (hcard : Fintype.card ι = 2 * k) (hk : 0 < k)
    (T : Ω → (EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))
    (c : Ω → EuclideanSpace ℝ ι) {R : ℝ} (hR : 0 < R)
    (hjoint : Measurable (fun p : Ω × EuclideanSpace ℝ ι => T p.1 p.2 - c p.1)) :
    (μ.prod (euclideanGaussianLaw ι)) {p | ‖T p.1 p.2 - c p.1‖ ≤ R} ≤
      (∫⁻ ω, inverseJacobian (T ω) ∂μ) *
        ENNReal.ofReal ((R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) := by
  letI : IsProbabilityMeasure (euclideanGaussianLaw ι) := by
    unfold euclideanGaussianLaw
    exact Measure.isProbabilityMeasure_map ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).symm.measurable.aemeasurable
  have hS : MeasurableSet {p : Ω × EuclideanSpace ℝ ι | ‖T p.1 p.2 - c p.1‖ ≤ R} :=
    hjoint.norm measurableSet_Iic
  rw [Measure.prod_apply hS]
  calc _ ≤ ∫⁻ ω, inverseJacobian (T ω) *
      ENNReal.ofReal ((R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) ∂μ := by
        apply lintegral_mono
        intro ω
        dsimp only
        have heq : Prod.mk ω ⁻¹' {p : Ω × EuclideanSpace ℝ ι | ‖T p.1 p.2 - c p.1‖ ≤ R} =
            T ω ⁻¹' closedBall (c ω) R := by
          ext x
          simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_closedBall, dist_eq_norm]
        rw [heq]
        exact euclideanGaussian_linear_closedBall_le_extended hcard hk (T ω) (c ω) hR
    _ = _ := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.joint_euclideanGaussian_linear_closedBall_le
