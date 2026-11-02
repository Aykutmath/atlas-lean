import GaussianCoisometry
import MatrixWhitening
import GaussianMatrixOperator
import GaussianChiSquareTail

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoid.SmallBall
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.SparseSupport

/-- The block-row contraction representing multiplication by a fixed vector. -/
def rowContraction {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq ρ]
    (v : κ → ℝ) : Matrix ρ (ρ × κ) ℝ := fun i p => if i = p.1 then v p.2 else 0

theorem rowContraction_mul_transpose {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    [DecidableEq ρ] (v : κ → ℝ) (hv : ∑ j, (v j)^2 = 1) :
    rowContraction (ρ := ρ) v * (rowContraction (ρ := ρ) v).transpose = (1 : Matrix ρ ρ ℝ) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowContraction, Fintype.sum_prod_type]
  by_cases hik : i = k
  · subst k
    simp [← pow_two, hv, Matrix.one_apply]
  · simp [hik, Matrix.one_apply, ite_mul, mul_ite]

theorem rowContraction_coisometry {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    [DecidableEq ρ] [DecidableEq κ] (v : κ → ℝ) (hv : ∑ j, (v j)^2 = 1) :
    matrixCLM (rowContraction (ρ := ρ) v) ∘L
      ContinuousLinearMap.adjoint (matrixCLM (rowContraction v)) =
        ContinuousLinearMap.id ℝ _ := by
  rw [← matrixCLM_transpose, ← matrixCLM_mul, rowContraction_mul_transpose v hv,
    matrixCLM_one]

/-- Every row image is independent standard Gaussian. This is equality with
an actual product law, obtained from the proved coisometry law. -/
theorem gaussian_matrix_fixed_vector_law {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    [DecidableEq ρ] [DecidableEq κ] (v : κ → ℝ) (hv : ∑ j, (v j)^2 = 1) :
    (gaussianProductLaw (ρ × κ)).map (fun x => fun i => ∑ j, x (i,j) * v j) =
      gaussianProductLaw ρ := by
  let Q := matrixCLM (rowContraction (ρ := ρ) v)
  have hQ : (euclideanGaussianLaw (ρ × κ)).map Q = euclideanGaussianLaw ρ :=
    euclideanGaussianLaw_map_coisometry Q (rowContraction_coisometry v hv)
  have hQe := congrArg (fun μ : Measure (EuclideanSpace ℝ ρ) =>
    μ.map ((MeasurableEquiv.toLp 2 (ρ → ℝ)).symm)) hQ
  rw [euclideanGaussianLaw, Measure.map_map Q.continuous.measurable
    (MeasurableEquiv.toLp 2 ((ρ × κ) → ℝ)).measurable,
    Measure.map_map ((MeasurableEquiv.toLp 2 (ρ → ℝ)).symm).measurable
      (Q.continuous.measurable.comp (MeasurableEquiv.toLp 2 ((ρ × κ) → ℝ)).measurable),
    euclideanGaussianLaw, Measure.map_map ((MeasurableEquiv.toLp 2 (ρ → ℝ)).symm).measurable
      (MeasurableEquiv.toLp 2 (ρ → ℝ)).measurable] at hQe
  simp only [MeasurableEquiv.self_comp_symm, MeasurableEquiv.symm_comp_self, Measure.map_id] at hQe
  convert hQe using 1
  congr 1
  funext x i
  change (∑ j, x (i,j) * v j) = ∑ p : ρ × κ, (if i = p.1 then v p.2 else 0) * x p
  simp [Fintype.sum_prod_type, ite_mul, mul_comm]

/-- Fixed-vector matrix output has precisely the standard product law; in
particular the output coordinates are independent, rather than just marginally normal. -/
theorem gaussianMatrixCLM_fixed_vector_law (h n : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    (gaussianProductLaw (Fin h × Fin n)).map
      (fun x => ((MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).symm) (gaussianMatrixCLM h n x v)) =
        gaussianProductLaw (Fin h) := by
  have hv₂ : ∑ j, (v j)^2 = 1 := by
    simpa [hv, Real.norm_eq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) v).symm
  convert gaussian_matrix_fixed_vector_law (ρ := Fin h) (fun j => v j) hv₂ using 1
  congr 1

/-- Actual fixed-vector chi-square tail for the Euclidean Gaussian matrix. -/
theorem gaussianMatrixCLM_fixed_vector_tail (h n : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    (gaussianProductLaw (Fin h × Fin n)).real
      {x | (h : ℝ)/4 ≤ |‖gaussianMatrixCLM h n x v‖^2 - h|} ≤
        2 * Real.exp (-(h : ℝ)/256) := by
  let f := fun x => ((MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).symm) (gaussianMatrixCLM h n x v)
  have hf : Measurable f := ((MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).symm).measurable.comp
    (((gaussianMatrixCLM_continuous h n).clm_apply continuous_const).measurable)
  have hlaw := gaussianMatrixCLM_fixed_vector_law h n v hv
  have htail := GaussianEllipsoidCandidate.gaussian_square_sum_two_sided (ι := Fin h)
  rw [← hlaw, Measure.real, Measure.map_apply hf (measurableSet_le measurable_const (by fun_prop))] at htail
  simp only [Fintype.card_fin] at htail
  convert htail using 1
  congr 1
  ext x
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin h => ℝ) (gaussianMatrixCLM h n x v)
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Fintype.card_fin]
  rw [hn]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

end GaussianEllipsoid.SparseSupport
