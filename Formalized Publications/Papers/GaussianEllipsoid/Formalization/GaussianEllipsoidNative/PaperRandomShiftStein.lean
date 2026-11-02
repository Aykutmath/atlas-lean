import PaperSymmetricSteinSource
import Mathlib.Probability.Independence.Integration

/-! New reconstruction of independent random-shift transport. Every bound is
on derivatives times Gaussian polynomials; no moment assumption on M appears. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition PaperAutomaticDerivativeSlices
open GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open GaussianEllipsoid.PaperSymmetricPullback
open scoped BigOperators InnerProductSpace ContDiff
namespace GaussianEllipsoid.PaperRandomShiftStein
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)

lemma continuous_zSym {d : ℕ} : Continuous (zSym (d := d)) := by
  have he (w : Fin d → ℝ) : zSym w =
      synth d (polynomialFamily (sourcePolynomials (0 : SymFrob d) 1) w) := by
    simpa using (source_field_reconstruction (0 : SymFrob d) 1 w).symm
  rw [show zSym (d := d) = (fun w => synth d (polynomialFamily (sourcePolynomials (0 : SymFrob d) 1) w)) from funext he]
  exact (synth d).continuous.comp (polynomialFamily _).continuous

lemma continuous_source_derivative {d : ℕ} {Φ : SymFrob d → ℝ}
    (D : SourceDerivatives Φ) (s : ℝ) (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3)
    (u : Fin n → SymFrob d) :
    Continuous (fun z : SymFrob d × (Fin d → ℝ) =>
      iteratedFDeriv ℝ n Φ (z.1+s • zSym z.2) u) := by
  have hd := (D.smooth.iteratedFDeriv_right (i := n) (m := 0) (by simpa using hn)).continuous
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => SymFrob d) ℝ u).continuous.comp hd).comp
    (continuous_fst.add ((continuous_zSym.comp continuous_snd).const_smul s))

lemma source_derivative_norm_le {d : ℕ} {Φ : SymFrob d → ℝ}
    (n : ℕ) (u : Fin n → SymFrob d) (C : ℝ)
    (hC : ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C) (x : SymFrob d) :
    ‖iteratedFDeriv ℝ n Φ x u‖ ≤ C * ∏ i, ‖u i‖ :=
  ((iteratedFDeriv ℝ n Φ x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (hC x) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

lemma integrable_source_derivative_fixed {d : ℕ} {Φ : SymFrob d → ℝ}
    (D : SourceDerivatives Φ) (M : SymFrob d) (s : ℝ)
    (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3) (u : Fin n → SymFrob d) (C : ℝ)
    (hC : ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C) (P : MvPolynomial (Fin d) ℝ) :
    Integrable (fun w => MvPolynomial.eval w P *
      iteratedFDeriv ℝ n Φ (M+s • zSym w) u) (gaussianProductLaw (Fin d)) := by
  have hp := (gaussianProductLaw_integrable_polynomial P).norm.mul_const (C * ∏ i, ‖u i‖)
  apply hp.mono'
  · exact ((polynomial_continuous_eval P).mul
      ((continuous_source_derivative D s n hn u).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (source_derivative_norm_le n u C hC _) (norm_nonneg _)

lemma integrable_source_derivative_product {d : ℕ} {Φ : SymFrob d → ℝ}
    (D : SourceDerivatives Φ) (ν : Measure (SymFrob d)) [IsProbabilityMeasure ν]
    (s : ℝ) (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3) (u : Fin n → SymFrob d) (C : ℝ)
    (hC : ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C) (P : MvPolynomial (Fin d) ℝ) :
    Integrable (fun z : SymFrob d × (Fin d → ℝ) => MvPolynomial.eval z.2 P *
      iteratedFDeriv ℝ n Φ (z.1+s • zSym z.2) u) (ν.prod (gaussianProductLaw (Fin d))) := by
  have hp := ((gaussianProductLaw_integrable_polynomial P).norm.mul_const
    (C * ∏ i, ‖u i‖)).comp_snd ν
  apply hp.mono'
  · exact (((polynomial_continuous_eval P).comp continuous_snd).mul
      (continuous_source_derivative D s n hn u)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (source_derivative_norm_le n u C hC _) (norm_nonneg _)

/-- Independence transports to a product law; Gaussian domination supplies
integrability before invoking Fubini. -/
theorem independent_source_derivative {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {Φ : SymFrob d → ℝ} (D : SourceDerivatives Φ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Ω → SymFrob d) (W : Ω → Fin d → ℝ)
    (hM : AEMeasurable M μ) (hW : AEMeasurable W μ)
    (hind : IndepFun M W μ) (hlaw : μ.map W = gaussianProductLaw (Fin d))
    (s : ℝ) (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3) (u : Fin n → SymFrob d) (C : ℝ)
    (hC : ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C) (P : MvPolynomial (Fin d) ℝ) :
    Integrable (fun o => MvPolynomial.eval (W o) P *
      iteratedFDeriv ℝ n Φ (M o+s • zSym (W o)) u) μ ∧
    (∫ o, MvPolynomial.eval (W o) P * iteratedFDeriv ℝ n Φ (M o+s • zSym (W o)) u ∂μ) =
      ∫ m, ∫ w, MvPolynomial.eval w P * iteratedFDeriv ℝ n Φ (m+s • zSym w) u
        ∂gaussianProductLaw (Fin d) ∂μ.map M := by
  letI := Measure.isProbabilityMeasure_map hM
  let F := fun z : SymFrob d × (Fin d → ℝ) => MvPolynomial.eval z.2 P *
    iteratedFDeriv ℝ n Φ (z.1+s • zSym z.2) u
  have hl : μ.map (fun o => (M o, W o)) = (μ.map M).prod (gaussianProductLaw (Fin d)) := by
    rw [hind.map_prod_eq_prod_map_map hM hW, hlaw]
  have hi : Integrable F ((μ.map M).prod (gaussianProductLaw (Fin d))) :=
    integrable_source_derivative_product D (μ.map M) s n hn u C hC P
  have him : Integrable F (μ.map (fun o => (M o, W o))) := by rwa [hl]
  constructor
  · exact (integrable_map_measure him.aestronglyMeasurable (hM.prodMk hW)).mp him
  · rw [← integral_map (hM.prodMk hW) him.aestronglyMeasurable, hl, integral_prod F hi]

/-- The fixed-shift coordinate identity integrated over the arbitrary independent
shift law. No bound on, or integrability of, the potential is assumed. -/
theorem random_symmetric_affine_second_stein {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (Φ : SymFrob d → ℝ) (D : SourceDerivatives Φ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Ω → SymFrob d) (W : Ω → Fin d → ℝ)
    (hM : AEMeasurable M μ) (hW : AEMeasurable W μ)
    (hind : IndepFun M W μ) (hlaw : μ.map W = gaussianProductLaw (Fin d))
    (s : ℝ) (a : Index d) :
    (∫ o, MvPolynomial.eval (W o) (centeredQuadratic (PaperNormalizedSecondStein.rowMatrix (qMatrix a))) *
      iteratedFDeriv ℝ 1 Φ (M o+s • zSym (W o)) (fun i => qSym d (oneDirection a i)) ∂μ) =
    ∑ b, (s * Matrix.trace (qMatrix a*qMatrix b) *
      (∫ o, iteratedFDeriv ℝ 2 Φ (M o+s • zSym (W o))
        (fun i => qSym d (twoDirections a b i)) ∂μ) +
      s^2 * Real.sqrt 2 * ∑ c, ∫ o,
        MvPolynomial.eval (W o) (rawQuadratic (qMatrix b*qMatrix a*qMatrix c)) *
        iteratedFDeriv ℝ 3 Φ (M o+s • zSym (W o))
          (fun i => qSym d (threeDirections a b c i)) ∂μ) := by
  letI := Measure.isProbabilityMeasure_map hM
  have h1 := (independent_source_derivative D μ M W hM hW hind hlaw s 1 (by norm_num)
    (fun i => qSym d (oneDirection a i)) D.C1 D.bound1
    (centeredQuadratic (PaperNormalizedSecondStein.rowMatrix (qMatrix a)))).2
  have h2 (b : Index d) := (independent_source_derivative D μ M W hM hW hind hlaw s 2 (by norm_num)
    (fun i => qSym d (twoDirections a b i)) D.C2 D.bound2 (1 : MvPolynomial (Fin d) ℝ)).2
  have h3 (b c : Index d) := (independent_source_derivative D μ M W hM hW hind hlaw s 3 (by norm_num)
    (fun i => qSym d (threeDirections a b c i)) D.C3 D.bound3
    (rawQuadratic (qMatrix b*qMatrix a*qMatrix c))).2
  simp only [map_one, one_mul] at h2
  rw [h1]
  simp_rw [h2, h3]
  have hi2 (b : Index d) := (integrable_source_derivative_product D (μ.map M) s 2 (by norm_num)
    (fun i => qSym d (twoDirections a b i)) D.C2 D.bound2 (1 : MvPolynomial (Fin d) ℝ)).integral_prod_left
  have hi3 (b c : Index d) := (integrable_source_derivative_product D (μ.map M) s 3 (by norm_num)
    (fun i => qSym d (threeDirections a b c i)) D.C3 D.bound3
    (rawQuadratic (qMatrix b*qMatrix a*qMatrix c))).integral_prod_left
  simp only [map_one, one_mul] at hi2
  simp_rw [symmetric_affine_second_stein Φ D]
  have hsum := integral_finsetSum Finset.univ (fun b _ =>
    ((hi2 b).const_mul (s * Matrix.trace (qMatrix a*qMatrix b))).add
    ((integrable_finsetSum Finset.univ (fun c _ => hi3 b c)).const_mul (s^2 * Real.sqrt 2)))
  simp only [Pi.add_apply] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_add ((hi2 b).const_mul (s * Matrix.trace (qMatrix a*qMatrix b)))
    ((integrable_finsetSum Finset.univ (fun c _ => hi3 b c)).const_mul (s^2 * Real.sqrt 2))]
  simp only [integral_const_mul]
  rw [integral_finsetSum Finset.univ (fun c _ => hi3 b c)]

#print axioms independent_source_derivative
#print axioms random_symmetric_affine_second_stein
end GaussianEllipsoid.PaperRandomShiftStein
