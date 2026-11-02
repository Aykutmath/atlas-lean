import PaperSymmetricTensorExpansion
import PaperRandomShiftStein
import Mathlib.Analysis.Calculus.Gradient.Basic

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory GaussianTensorMoments BMQuadraticStein
open PaperAutomaticDerivativeSlices
open GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open GaussianEllipsoid.PaperRandomShiftStein
open scoped BigOperators InnerProductSpace ContDiff
namespace GaussianEllipsoid.PaperSymmetricPullback
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)

def sourceLaplacian {d : ℕ} (Φ : SymFrob d → ℝ) (Y : SymFrob d) : ℝ :=
  ∑ a : Index d,iteratedFDeriv ℝ 2 Φ Y (fun i => qSym d (twoDirections a a i))

lemma source_gradient_coordinates {d : ℕ} (Φ : SymFrob d → ℝ) (Y Z : SymFrob d) :
    (fderiv ℝ Φ Y) Z = ∑ a : Index d,coordinates Z a *
      iteratedFDeriv ℝ 1 Φ Y (fun i => qSym d (oneDirection a i)) := by
  conv_lhs => rw [← synth_coordinates Z,synth_apply]
  simp only [map_sum,map_smul,smul_eq_mul,iteratedFDeriv_one_apply,oneDirection,Fin.cons_zero]

lemma third_directions_eq {d : ℕ} (a b c : Index d) :
    (fun i => qSym d (threeDirections a b c i))=
      Fin.cons (qSym d c) (Fin.cons (qSym d b) (Fin.cons (qSym d a) Fin.elim0)) := by
  ext i
  fin_cases i <;> rfl

/-- The literal deterministic-shift source identity, with the Frobenius
Laplacian and actual ordered-direction T_w, for arbitrary C3 Φ whose first
three derivatives are bounded. No bound or integrability of Φ is assumed. -/
theorem paper_second_stein_fixed {d : ℕ} (Φ : SymFrob d → ℝ)
    (D : SourceDerivatives Φ) (M : SymFrob d) (s : ℝ) :
    (∫ w, (fderiv ℝ Φ (M+s • zSym w)) (zSym w) ∂gaussianProductLaw (Fin d)) =
      s*(∫ w,sourceLaplacian Φ (M+s • zSym w) ∂gaussianProductLaw (Fin d)) +
      s^2*(∫ w,sourceTensorCorrection (iteratedFDeriv ℝ 3 Φ (M+s • zSym w)) w
        ∂gaussianProductLaw (Fin d)) := by
  let f1 := fun (a : Index d) (w : Fin d → ℝ) =>
    MvPolynomial.eval w (centeredQuadratic (PaperNormalizedSecondStein.rowMatrix (qMatrix a))) *
      iteratedFDeriv ℝ 1 Φ (M+s • zSym w) (fun i => qSym d (oneDirection a i))
  let f2 := fun (a b : Index d) (w : Fin d → ℝ) =>
    iteratedFDeriv ℝ 2 Φ (M+s • zSym w) (fun i => qSym d (twoDirections a b i))
  let f3 := fun (a b c : Index d) (w : Fin d → ℝ) =>
    MvPolynomial.eval w (rawQuadratic (qMatrix b*qMatrix a*qMatrix c)) *
      iteratedFDeriv ℝ 3 Φ (M+s • zSym w) (fun i => qSym d (threeDirections a b c i))
  have hi1 (a : Index d) : Integrable (f1 a) (gaussianProductLaw (Fin d)) :=
    integrable_source_derivative_fixed D M s 1 (by norm_num) _ D.C1 D.bound1 _
  have hi2 (a b : Index d) : Integrable (f2 a b) (gaussianProductLaw (Fin d)) := by
    simpa only [map_one,one_mul] using
      integrable_source_derivative_fixed D M s 2 (by norm_num)
        (fun i => qSym d (twoDirections a b i)) D.C2 D.bound2 (1 : MvPolynomial (Fin d) ℝ)
  have hi3 (a b c : Index d) : Integrable (f3 a b c) (gaussianProductLaw (Fin d)) :=
    integrable_source_derivative_fixed D M s 3 (by norm_num) _ D.C3 D.bound3 _
  have hlap : (∫ w,sourceLaplacian Φ (M+s • zSym w) ∂gaussianProductLaw (Fin d)) =
      ∑ a : Index d,∫ w,f2 a a w ∂gaussianProductLaw (Fin d) :=
    integral_finset_sum _ (fun a _ => hi2 a a)
  have htensor : (∫ w,sourceTensorCorrection (iteratedFDeriv ℝ 3 Φ (M+s • zSym w)) w
        ∂gaussianProductLaw (Fin d)) = Real.sqrt 2 *
      ∑ a : Index d,∑ b : Index d,∑ c : Index d,∫ w,f3 a b c w ∂gaussianProductLaw (Fin d) := by
    simp_rw [sourceTensorCorrection_coordinate]
    have hv (a b c : Index d) (w : Fin d → ℝ) :
        tri (iteratedFDeriv ℝ 3 Φ (M+s • zSym w)) (qSym d c) (qSym d b) (qSym d a)=
          iteratedFDeriv ℝ 3 Φ (M+s • zSym w) (fun i => qSym d (threeDirections a b c i)) := by
      rw [third_directions_eq]
      rfl
    simp_rw [hv]
    change (∫ w,Real.sqrt 2*∑ a,∑ b,∑ c,f3 a b c w ∂gaussianProductLaw (Fin d))=_
    rw [integral_const_mul,integral_finset_sum _ (fun a _ =>
      integrable_finset_sum _ (fun b _ => integrable_finset_sum _ (fun c _ => hi3 a b c)))]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_finset_sum _ (fun b _ => integrable_finset_sum _ (fun c _ => hi3 a b c))]
    apply Finset.sum_congr rfl
    intro b _
    exact integral_finset_sum _ (fun c _ => hi3 a b c)
  rw [hlap,htensor]
  have hleft (w : Fin d → ℝ) : (fderiv ℝ Φ (M+s • zSym w)) (zSym w)=∑ a,f1 a w := by
    rw [source_gradient_coordinates]
    simp only [coordinates_zSym,f1]
  simp_rw [hleft]
  rw [integral_finset_sum _ (fun a _ => hi1 a)]
  have hcoord (a : Index d) : (∫ w,f1 a w ∂gaussianProductLaw (Fin d)) =
    ∑ b,(s*Matrix.trace (qMatrix a*qMatrix b)*(∫ w,f2 a b w ∂gaussianProductLaw (Fin d))+
      s^2*Real.sqrt 2*∑ c,∫ w,f3 a b c w ∂gaussianProductLaw (Fin d)) :=
    symmetric_affine_second_stein Φ D M s a
  simp only [hcoord,qMatrix_trace,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero,
    ite_mul,zero_mul,Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp_rw [← Finset.mul_sum]
  ring

lemma symFrob_inner_matrix {d : ℕ} (U V : SymFrob d) :
    ⟪U,V⟫_ℝ=PaperSymmetricDirections.frobInner (matrix U) (matrix V) := by
  change (∑ j,∑ i,V.val j i*U.val j i) = ∑ i,∑ j,U.val j i*V.val j i
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma qSym_inner {d : ℕ} (a b : Index d) : ⟪qSym d a,qSym d b⟫_ℝ=if a=b then 1 else 0 := by
  rw [symFrob_inner_matrix,matrix_qSym,matrix_qSym,
    PaperSymmetricBasis.Q_gram _ _ _ _ a.property b.property]
  congr 1
  exact propext (by simp only [Subtype.ext_iff,Prod.ext_iff])

lemma sourceLaplacian_eq_upper {d : ℕ} (Φ : SymFrob d → ℝ) (Y : SymFrob d) :
    sourceLaplacian Φ Y=∑ a : Fin d,∑ b : Fin d,if a ≤ b then
      iteratedFDeriv ℝ 2 Φ Y (fun _ : Fin 2 =>
        ofMatrix (PaperSymmetricDirections.Q a b) (PaperSymmetricBasis.Q_transpose a b)) else 0 := by
  have hd (a : Index d) : (fun i => qSym d (twoDirections a a i))=(fun _ : Fin 2 => qSym d a) := by
    ext i
    fin_cases i <;> rfl
  unfold sourceLaplacian
  simp_rw [hd]
  have hs := Finset.sum_subtype (p := fun a : Fin d × Fin d => a.1 ≤ a.2) (F := inferInstance)
    (Finset.univ.filter (fun a : Fin d × Fin d => a.1 ≤ a.2)) (by intro a; simp)
    (fun a : Fin d × Fin d => iteratedFDeriv ℝ 2 Φ Y (fun _ : Fin 2 =>
      ofMatrix (PaperSymmetricDirections.Q a.1 a.2) (PaperSymmetricBasis.Q_transpose a.1 a.2)))
  unfold qSym
  rw [← hs,Finset.sum_filter,Fintype.sum_prod_type]

/-- The source's gradient pairing notation is the actual Frobenius gradient. -/
theorem paper_second_stein_gradient {d : ℕ} (Φ : SymFrob d → ℝ)
    (D : SourceDerivatives Φ) (M : SymFrob d) (s : ℝ) :
    (∫ w, ⟪zSym w,_root_.gradient Φ (M+s • zSym w)⟫_ℝ ∂gaussianProductLaw (Fin d)) =
      s*(∫ w,sourceLaplacian Φ (M+s • zSym w) ∂gaussianProductLaw (Fin d)) +
      s^2*(∫ w,sourceTensorCorrection (iteratedFDeriv ℝ 3 Φ (M+s • zSym w)) w
        ∂gaussianProductLaw (Fin d)) := by
  simpa only [inner_gradient_right,starRingEnd_apply,star_trivial] using paper_second_stein_fixed Φ D M s

#print axioms paper_second_stein_fixed
#print axioms paper_second_stein_gradient
#print axioms sourceLaplacian_eq_upper
#print axioms qSym_inner
end GaussianEllipsoid.PaperSymmetricPullback
