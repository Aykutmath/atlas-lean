import PaperSymmetricSteinAggregate

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open PaperAutomaticDerivativeSlices
open GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open GaussianEllipsoid.PaperRandomShiftStein
open scoped BigOperators InnerProductSpace ContDiff
open GaussianEllipsoid.PaperSymmetricPullback
namespace GaussianEllipsoid.PaperRandomShiftStein
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)

/-- The literal source identity on an arbitrary probability space, for an
independent a.e.-measurable random shift M. All required integrability is proved
from uniform first-three-derivative bounds and Gaussian polynomial moments.
No moment of M, no bound or integrability of Φ, and no fourth derivative are
assumed. The theorem holds for every real s, including s = 0. -/
theorem paper_second_stein_random {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (Φ : SymFrob d → ℝ) (D : SourceDerivatives Φ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Ω → SymFrob d) (W : Ω → Fin d → ℝ)
    (hM : AEMeasurable M μ) (hW : AEMeasurable W μ)
    (hind : IndepFun M W μ) (hlaw : μ.map W = gaussianProductLaw (Fin d))
    (s : ℝ) :
    (∫ o, (fderiv ℝ Φ (M o+s • zSym (W o))) (zSym (W o)) ∂μ) =
      s*(∫ o,sourceLaplacian Φ (M o+s • zSym (W o)) ∂μ) +
      s^2*(∫ o,sourceTensorCorrection (iteratedFDeriv ℝ 3 Φ (M o+s • zSym (W o))) (W o)
        ∂μ) := by
  let f1 := fun (a : Index d) (o : Ω) =>
    MvPolynomial.eval (W o) (centeredQuadratic (PaperNormalizedSecondStein.rowMatrix (qMatrix a))) *
      iteratedFDeriv ℝ 1 Φ (M o+s • zSym (W o)) (fun i => qSym d (oneDirection a i))
  let f2 := fun (a b : Index d) (o : Ω) =>
    iteratedFDeriv ℝ 2 Φ (M o+s • zSym (W o)) (fun i => qSym d (twoDirections a b i))
  let f3 := fun (a b c : Index d) (o : Ω) =>
    MvPolynomial.eval (W o) (rawQuadratic (qMatrix b*qMatrix a*qMatrix c)) *
      iteratedFDeriv ℝ 3 Φ (M o+s • zSym (W o)) (fun i => qSym d (threeDirections a b c i))
  have hi1 (a : Index d) : Integrable (f1 a) μ :=
    (independent_source_derivative D μ M W hM hW hind hlaw s 1 (by norm_num) _ D.C1 D.bound1 _).1
  have hi2 (a b : Index d) : Integrable (f2 a b) μ := by
    simpa only [map_one,one_mul] using
      (independent_source_derivative D μ M W hM hW hind hlaw s 2 (by norm_num)
        (fun i => qSym d (twoDirections a b i)) D.C2 D.bound2 (1 : MvPolynomial (Fin d) ℝ)).1
  have hi3 (a b c : Index d) : Integrable (f3 a b c) μ :=
    (independent_source_derivative D μ M W hM hW hind hlaw s 3 (by norm_num) _ D.C3 D.bound3 _).1
  have hlap : (∫ o,sourceLaplacian Φ (M o+s • zSym (W o)) ∂μ) =
      ∑ a : Index d,∫ o,f2 a a o ∂μ :=
    integral_finsetSum _ (fun a _ => hi2 a a)
  have htensor : (∫ o,sourceTensorCorrection (iteratedFDeriv ℝ 3 Φ (M o+s • zSym (W o))) (W o)
        ∂μ) = Real.sqrt 2 *
      ∑ a : Index d,∑ b : Index d,∑ c : Index d,∫ o,f3 a b c o ∂μ := by
    simp_rw [sourceTensorCorrection_coordinate]
    have hv (a b c : Index d) (o : Ω) :
        tri (iteratedFDeriv ℝ 3 Φ (M o+s • zSym (W o))) (qSym d c) (qSym d b) (qSym d a)=
          iteratedFDeriv ℝ 3 Φ (M o+s • zSym (W o)) (fun i => qSym d (threeDirections a b c i)) := by
      rw [third_directions_eq]
      rfl
    simp_rw [hv]
    change (∫ o,Real.sqrt 2*∑ a,∑ b,∑ c,f3 a b c o ∂μ)=_
    rw [integral_const_mul,integral_finsetSum _ (fun a _ =>
      integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => hi3 a b c)))]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => hi3 a b c))]
    apply Finset.sum_congr rfl
    intro b _
    exact integral_finsetSum _ (fun c _ => hi3 a b c)
  rw [hlap,htensor]
  have hleft (o : Ω) : (fderiv ℝ Φ (M o+s • zSym (W o))) (zSym (W o))=∑ a,f1 a o := by
    rw [source_gradient_coordinates]
    simp only [coordinates_zSym,f1]
  simp_rw [hleft]
  rw [integral_finsetSum _ (fun a _ => hi1 a)]
  have hcoord (a : Index d) : (∫ o,f1 a o ∂μ) =
    ∑ b,(s*Matrix.trace (qMatrix a*qMatrix b)*(∫ o,f2 a b o ∂μ)+
      s^2*Real.sqrt 2*∑ c,∫ o,f3 a b c o ∂μ) :=
    random_symmetric_affine_second_stein Φ D μ M W hM hW hind hlaw s a
  simp only [hcoord,qMatrix_trace,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero,
    ite_mul,zero_mul,Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp_rw [← Finset.mul_sum]
  ring

/-- The actual Frobenius gradient, source upper-Q Laplacian, and literal
ordered B_a,B_b,S_ab contraction in the displayed random-M identity. -/
theorem paper_second_stein_random_gradient {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (Φ : SymFrob d → ℝ) (D : SourceDerivatives Φ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Ω → SymFrob d) (W : Ω → Fin d → ℝ)
    (hM : AEMeasurable M μ) (hW : AEMeasurable W μ)
    (hind : IndepFun M W μ) (hlaw : μ.map W = gaussianProductLaw (Fin d))
    (s : ℝ) :
    (∫ o, ⟪zSym (W o),_root_.gradient Φ (M o+s • zSym (W o))⟫_ℝ ∂μ) =
      s*(∫ o,sourceLaplacian Φ (M o+s • zSym (W o)) ∂μ) +
      s^2*(∫ o,sourceTensorCorrection
        (iteratedFDeriv ℝ 3 Φ (M o+s • zSym (W o))) (W o) ∂μ) := by
  simpa only [inner_gradient_right,starRingEnd_apply,star_trivial] using
    paper_second_stein_random Φ D μ M W hM hW hind hlaw s

/-- All three literal source expectations are genuine integrable functions
on the actual probability space; this does not use integrability of M or Φ. -/
theorem paper_second_stein_random_integrable {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (Φ : SymFrob d → ℝ) (D : SourceDerivatives Φ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Ω → SymFrob d) (W : Ω → Fin d → ℝ)
    (hM : AEMeasurable M μ) (hW : AEMeasurable W μ)
    (hind : IndepFun M W μ) (hlaw : μ.map W = gaussianProductLaw (Fin d))
    (s : ℝ) :
    Integrable (fun o => ⟪zSym (W o),_root_.gradient Φ (M o+s • zSym (W o))⟫_ℝ) μ ∧
    Integrable (fun o => sourceLaplacian Φ (M o+s • zSym (W o))) μ ∧
    Integrable (fun o => sourceTensorCorrection
      (iteratedFDeriv ℝ 3 Φ (M o+s • zSym (W o))) (W o)) μ := by
  constructor
  · simp only [inner_gradient_right,starRingEnd_apply,star_trivial,
      source_gradient_coordinates,coordinates_zSym]
    exact integrable_finsetSum _ (fun a _ =>
      (independent_source_derivative D μ M W hM hW hind hlaw s 1 (by norm_num)
        (fun i => qSym d (oneDirection a i)) D.C1 D.bound1
        (centeredQuadratic (PaperNormalizedSecondStein.rowMatrix (qMatrix a)))).1)
  constructor
  · unfold sourceLaplacian
    apply integrable_finsetSum
    intro a _
    simpa only [map_one,one_mul] using
      (independent_source_derivative D μ M W hM hW hind hlaw s 2 (by norm_num)
        (fun i => qSym d (twoDirections a a i)) D.C2 D.bound2
        (1 : MvPolynomial (Fin d) ℝ)).1
  · simp_rw [sourceTensorCorrection_coordinate]
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro a _
    apply integrable_finsetSum
    intro b _
    apply integrable_finsetSum
    intro c _
    simpa only [tri,third_directions_eq] using
      (independent_source_derivative D μ M W hM hW hind hlaw s 3 (by norm_num)
        (fun i => qSym d (threeDirections a b c i)) D.C3 D.bound3
        (rawQuadratic (qMatrix b*qMatrix a*qMatrix c))).1

#print axioms paper_second_stein_random_integrable
#print axioms paper_second_stein_random
#print axioms paper_second_stein_random_gradient
end GaussianEllipsoid.PaperRandomShiftStein
