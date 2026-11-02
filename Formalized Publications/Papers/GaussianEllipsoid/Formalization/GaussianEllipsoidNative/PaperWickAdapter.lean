import PaperEmpiricalSupAdapter
import BMQuadraticStein

noncomputable section
open MeasureTheory GaussianTensorMoments MvPolynomial BMQuadraticStein
open scoped BigOperators
namespace GaussianEllipsoid.PaperWickAdapter
open PaperEmpiricalSupAdapter

/-- Literal polynomial-to-quadratic bridge, preserving diagonal centering. -/
theorem eval_centered_eq_source {p : ℕ} (A : Square p) (x : Vector p) :
    eval x (centeredQuadratic A) = quadratic A x-Matrix.trace A := by
  rw [eval_centeredQuadratic]
  congr 1
  unfold quadratic Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Paper Wick covariance for the exact normalized centered rank-one row. -/
theorem paper_wick_covariance {p : ℕ} (A B : Square p)
    (hA : A.transpose=A) (hB : B.transpose=B) :
    (∫ x : Vector p,
      (∑ i, ∑ j, centeredOuter x i j*A i j)*
      (∑ i, ∑ j, centeredOuter x i j*B i j) ∂gaussianVectorLaw p) =
      ∑ i, ∑ j, A i j*B i j := by
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have he (x : Vector p) :
      (∑ i, ∑ j, centeredOuter x i j*A i j)*
      (∑ i, ∑ j, centeredOuter x i j*B i j) =
      eval x (centeredQuadratic A*centeredQuadratic B)/2 := by
    rw [centeredOuter_pairing,centeredOuter_pairing,map_mul,
      eval_centered_eq_source,eval_centered_eq_source]
    rw [div_mul_div_comm,← pow_two,hs]
  simp_rw [he]
  rw [integral_div]
  have hc : (∫ x : Vector p, eval x (centeredQuadratic A*centeredQuadratic B)
      ∂gaussianVectorLaw p) = 2*(∑ i, ∑ j, A i j*B i j) := by
    simpa only [expectation,LinearMap.coe_mk,AddHom.coe_mk,gaussianVectorLaw,gaussianProductLaw]
      using expectation_centeredQuadratic_covariance_symmetric A B hB
  rw [hc]
  ring

/-- The coordinate Frobenius pairing is exactly Tr(AB) on symmetric inputs. -/
theorem frobenius_pairing_eq_trace {p : ℕ} (A B : Square p) (hB : B.transpose=B) :
    (∑ i, ∑ j, A i j*B i j) = Matrix.trace (A*B) := by
  have hb (i j : Fin p) : B j i=B i j := congrFun (congrFun hB i) j
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  simp_rw [hb]

#print axioms paper_wick_covariance
#print axioms frobenius_pairing_eq_trace
end GaussianEllipsoid.PaperWickAdapter
