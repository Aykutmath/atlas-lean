import BMFiniteGroundState
import BMExpectationLimits
import BMGaussianEquivalent

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMFiniteGibbsTest BMFiniteGibbsHessian
open BMProductLogPartition BMFiniteGibbsReplacement BMGibbsRowReplacement BMActualFiniteReplacement
open BMFiniteGroundState BMGaussianEquivalent Filter
open scoped BigOperators BoundedContinuousFunction

namespace BMFiniteUniversality

/-- The scalar smoothness data already imply the Lipschitz estimate needed for
the operator-net approximation; it is not an additional analytic assumption. -/
theorem potential_lipschitz (P : Data2 Unit) (x y : ℝ) :
    |P.potential x-P.potential y| ≤ ‖P.potentialDeriv‖*|x-y| := by
  have hL : LipschitzWith ‖P.potentialDeriv‖₊ P.potential := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (P.hasDeriv t).differentiableAt)
    intro t
    rw [(P.hasDeriv t).deriv]
    exact P.potentialDeriv.nnnorm_coe_le_nnnorm t
  simpa only [Real.dist_eq,coe_nnnorm] using! hL.dist_le_mul x y

/-- A fixed scalar bounded C² potential, arbitrary inverse temperature, and
uniform prior on the current finite state set. -/
def modelData {κ : Type*} [Fintype κ] [Nonempty κ]
    (P : Data2 Unit) (β : ℝ) (hβ : 0 ≤ β) : Data2 κ where
  weight := fun _ => (Fintype.card κ : ℝ)⁻¹
  weight_nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  weight_sum := by simp [ne_of_gt (Fintype.card_pos (α := κ))]
  potential := P.potential
  potentialDeriv := P.potentialDeriv
  hasDeriv := P.hasDeriv
  beta := β
  beta_nonneg := hβ
  potentialSecond := P.potentialSecond
  hasDeriv_second := P.hasDeriv_second

def quadraticGroundExpectation {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Data2 Unit) (d n : ℕ) (A : κ → Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∫ x : Fin (n+1) → (Fin d → ℝ),
    ground (modelData (κ := κ) P 1 (by norm_num)).toData ((d:ℝ)^2)
      (fun i => polynomialFamily (fun a => normalizedQuadratic d (A a)) (x i))
    ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin d))

def goeGroundExpectation {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Data2 Unit) (d n : ℕ) (A : κ → Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∫ z : Fin (n+1) → (Fin (d*d) → ℝ),
    ground (modelData (κ := κ) P 1 (by norm_num)).toData ((d:ℝ)^2)
      (fun i a => Matrix.trace (symmetrizedGaussianMatrix d (z i)*A a))
    ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin (d*d)))

/-- Explicit finite comparison with the actual symmetric Gaussian matrix,
without a remaining covariance-match premise. -/
theorem finite_goe_ground_comparison {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Data2 Unit) (β : ℝ) (hβ : 0 < β) {d : ℕ} (hd : 0 < d) (n : ℕ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hAsym : ∀ a, (A a).transpose = A a)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ a, spectralNorm (A a) ≤ K) :
    |quadraticGroundExpectation P d n A-goeGroundExpectation P d n A| ≤
      ((n+1 : ℕ)*replacementError (modelData (κ := Unit) P β hβ.le) K d)/(β*(d:ℝ)^2) +
        2*(Real.log (Fintype.card κ : ℝ)/(β*(d:ℝ)^2)) := by
  have h := actual_finite_ground_replacement (modelData (κ := κ) P β hβ.le) hβ A hAsym
    (fun a => gaussianCoefficients (A a))
    (fun a b => gaussianCoefficients_covariance (A a) (A b) (hAsym b)) hd hK hA n
  simpa only [quadraticGroundExpectation,goeGroundExpectation,ground,energy,rowSum,
    modelData,polynomialFamily,ContinuousMap.coe_mk,
    trace_symmetrizedGaussianMatrix_mul _ (hAsym _),replacementError,
    diagonalPriorConstant,pairPriorConstant] using! h

/-- Sample ratio and net entropy reduce the finite comparison to the form
needed for taking d→∞ first and β→∞ second. -/
theorem finite_goe_ground_comparison_of_entropy
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Data2 Unit) (β : ℝ) (hβ : 0 < β) {d : ℕ} (hd : 0 < d) (n : ℕ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hAsym : ∀ a, (A a).transpose = A a)
    {K α C : ℝ} (hK : 0 ≤ K) (hA : ∀ a, spectralNorm (A a) ≤ K)
    (hn : (n+1 : ℕ) ≤ α*(d:ℝ)^2)
    (hcard : Real.log (Fintype.card κ : ℝ) ≤ C*(d:ℝ)^2) :
    |quadraticGroundExpectation P d n A-goeGroundExpectation P d n A| ≤
      (α/β)*replacementError (modelData (κ := Unit) P β hβ.le) K d + (2*C)/β := by
  have hv : 0 < (d:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hd)
  have he := replacementError_nonneg (modelData (κ := Unit) P β hβ.le) K d
  apply (finite_goe_ground_comparison P β hβ hd n A hAsym hK hA).trans
  have hfirst : ((n+1 : ℕ)*replacementError (modelData (κ := Unit) P β hβ.le) K d)/(β*(d:ℝ)^2) ≤
      (α/β)*replacementError (modelData (κ := Unit) P β hβ.le) K d := by
    apply (div_le_iff₀ (mul_pos hβ hv)).2
    convert! mul_le_mul_of_nonneg_right hn he using 1 <;> field_simp <;> ring
  have hsecond : Real.log (Fintype.card κ : ℝ)/(β*(d:ℝ)^2) ≤ C/β := by
    apply (div_le_iff₀ (mul_pos hβ hv)).2
    convert! hcard using 1 <;> field_simp <;> ring
  have h := add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (by norm_num : (0:ℝ) ≤ 2))
  convert! h using 1 <;> ring

/-- Expectation-only finite-net ground-state universality. State sets can grow
with d; their sole size condition is log card≤C d². Every probabilistic
comparison in this theorem is proved from the actual quadratic and Gaussian
source laws. No CLT, replacement, or free-energy universality is assumed. -/
theorem finite_ground_expectation_universality
    (κ : ℕ → Type*) [∀ d, Fintype (κ d)] [∀ d, DecidableEq (κ d)] [∀ d, Nonempty (κ d)]
    (P : Data2 Unit) (n : ℕ → ℕ)
    (A : (d : ℕ) → κ d → Matrix (Fin d) (Fin d) ℝ)
    (hAsym : ∀ d a, (A d a).transpose = A d a)
    {K α C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ d a, spectralNorm (A d a) ≤ K)
    (hn : ∀ d, 0 < d → (n d+1 : ℕ) ≤ α*(d:ℝ)^2)
    (hcard : ∀ d, 0 < d → Real.log (Fintype.card (κ d) : ℝ) ≤ C*(d:ℝ)^2) :
    Tendsto (fun d => |quadraticGroundExpectation P d (n d) (A d)-
      goeGroundExpectation P d (n d) (A d)|) atTop (nhds 0) := by
  apply BMExpectationLimits.tendsto_zero_of_temperature_comparison _ (2*C)
    (fun _ => abs_nonneg _) (by positivity)
  intro β hβ
  refine ⟨fun d => (α/β)*replacementError (modelData (κ := Unit) P β hβ.le) K d, ?_, ?_⟩
  · simpa only [mul_zero] using
      (replacementError_tendsto_zero (modelData (κ := Unit) P β hβ.le) K).const_mul (α/β)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    exact finite_goe_ground_comparison_of_entropy P β hβ hd (n d) (A d) (hAsym d) hK
      (hA d) (hn d hd) (hcard d hd)

#print axioms finite_goe_ground_comparison
#print axioms finite_ground_expectation_universality
end BMFiniteUniversality
