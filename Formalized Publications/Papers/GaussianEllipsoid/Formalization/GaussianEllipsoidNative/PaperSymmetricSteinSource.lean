import PaperSymmetricPullback
import PaperWickAdapter

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory GaussianTensorMoments BMQuadraticStein BMSmoothQuadraticComposition
open PaperAutomaticDerivativeSlices PaperSymmetricDirections PaperSymmetricBasis
open PaperCavityThird PaperAffineSecondStein PaperNormalizedSecondStein BMAffineSmooth
open GaussianEllipsoid GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open GaussianEllipsoid.PaperEmpiricalSupAdapter GaussianEllipsoid.PaperWickAdapter
open scoped BigOperators InnerProductSpace ContDiff BoundedContinuousFunction
namespace GaussianEllipsoid.PaperSymmetricPullback
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)

def zSym {d : ℕ} (w : Fin d → ℝ) : SymFrob d := ofMatrix (centeredOuter w) (centeredOuter_transpose w)
def qMatrix {d : ℕ} (a : Index d) : Square d := Q a.val.1 a.val.2

def sourcePolynomials {d : ℕ} (M : SymFrob d) (s : ℝ) :=
  affinePolynomials s (coordinates M) (fun a : Index d => centeredQuadratic (rowMatrix (qMatrix a)))

lemma coordinates_zSym {d : ℕ} (w : Fin d → ℝ) (a : Index d) :
    coordinates (zSym w) a=MvPolynomial.eval w (centeredQuadratic (rowMatrix (qMatrix a))) := by
  unfold coordinates zSym
  rw [matrix_ofMatrix]
  change (∑ i, ∑ j, centeredOuter w i j*qMatrix a i j)=_
  rw [centeredOuter_pairing, rowMatrix, centeredQuadratic_smul]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, eval_centered_eq_source]
  ring

lemma source_field_reconstruction {d : ℕ} (M : SymFrob d) (s : ℝ) (w : Fin d → ℝ) :
    synth d (polynomialFamily (sourcePolynomials M s) w)=M+s • zSym w := by
  have he : polynomialFamily (sourcePolynomials M s) w=coordinates M+s • coordinates (zSym w) := by
    ext a
    simp only [sourcePolynomials,polynomialFamily,ContinuousMap.coe_mk,affinePolynomials,
      MvPolynomial.eval_add,MvPolynomial.eval_C,MvPolynomial.smul_eq_C_mul,MvPolynomial.eval_mul,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,coordinates_zSym,add_comm]
  rw [he,map_add,map_smul,synth_coordinates,synth_coordinates]

/-- All derivative coordinates in the twice-integrated identity are actual
Frobenius derivatives at the literal M+s(wwᵀ−I)/sqrt(2) matrix. -/
lemma source_derivative_slice {d : ℕ} {Φ : SymFrob d → ℝ} (D : SourceDerivatives Φ)
    (M : SymFrob d) (s : ℝ) (w : Fin d → ℝ) (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3)
    (u : Fin n → Index d) :
    PaperAutomaticDerivativeSlices.coordinateSlice (Φ ∘ synth d) n u (polynomialFamily (sourcePolynomials M s) w)=
      iteratedFDeriv ℝ n Φ (M+s • zSym w) (fun i => qSym d (u i)) := by
  rw [symmetric_coordinate_derivative D n hn,source_field_reconstruction]

/-- The checked two-IBP identity now applies to every source C3 potential,
with no boundedness of Φ and with exact actual first/second/third derivatives. -/
theorem symmetric_affine_second_stein {d : ℕ} (Φ : SymFrob d → ℝ)
    (D : SourceDerivatives Φ) (M : SymFrob d) (s : ℝ) (a : Index d) :
    (∫ w, MvPolynomial.eval w (centeredQuadratic (rowMatrix (qMatrix a))) *
      iteratedFDeriv ℝ 1 Φ (M+s • zSym w) (fun i => qSym d (oneDirection a i))
        ∂gaussianProductLaw (Fin d)) =
      ∑ b, (s * Matrix.trace (qMatrix a * qMatrix b) *
        (∫ w, iteratedFDeriv ℝ 2 Φ (M+s • zSym w)
          (fun i => qSym d (twoDirections a b i)) ∂gaussianProductLaw (Fin d)) +
        s^2 * Real.sqrt 2 * ∑ c,
          ∫ w, MvPolynomial.eval w (rawQuadratic (qMatrix b * qMatrix a * qMatrix c)) *
            iteratedFDeriv ℝ 3 Φ (M+s • zSym w)
              (fun i => qSym d (threeDirections a b c i)) ∂gaussianProductLaw (Fin d)) := by
  have h := normalized_affine_second_stein
    (gradientTest2 (pullbackDerivatives D (synth d)) a) qMatrix
    (fun b => Q_transpose b.val.1 b.val.2) a s (coordinates M)
  have h1 (w : Fin d → ℝ) := source_derivative_slice D M s w 1 (by norm_num) (oneDirection a)
  have h2 (b : Index d) (w : Fin d → ℝ) := source_derivative_slice D M s w 2 (by norm_num) (twoDirections a b)
  have h3 (b c : Index d) (w : Fin d → ℝ) := source_derivative_slice D M s w 3 (by norm_num) (threeDirections a b c)
  change (∫ w, MvPolynomial.eval w (centeredQuadratic (rowMatrix (qMatrix a))) *
      PaperAutomaticDerivativeSlices.coordinateSlice (Φ ∘ synth d) 1 (oneDirection a) (polynomialFamily (sourcePolynomials M s) w)
        ∂gaussianProductLaw (Fin d)) =
      ∑ b, (s * Matrix.trace (qMatrix a * qMatrix b) *
        (∫ w, MvPolynomial.eval w (1 : MvPolynomial (Fin d) ℝ) *
          PaperAutomaticDerivativeSlices.coordinateSlice (Φ ∘ synth d) 2 (twoDirections a b)
            (polynomialFamily (sourcePolynomials M s) w) ∂gaussianProductLaw (Fin d)) +
        s^2 * Real.sqrt 2 * ∑ c,
          ∫ w, MvPolynomial.eval w (rawQuadratic (qMatrix b * qMatrix a * qMatrix c)) *
            PaperAutomaticDerivativeSlices.coordinateSlice (Φ ∘ synth d) 3 (threeDirections a b c)
              (polynomialFamily (sourcePolynomials M s) w) ∂gaussianProductLaw (Fin d)) at h
  simpa only [h1,h2,h3,map_one,one_mul] using h

#print axioms source_field_reconstruction
#print axioms symmetric_affine_second_stein
#print axioms source_derivative_slice
end GaussianEllipsoid.PaperSymmetricPullback
