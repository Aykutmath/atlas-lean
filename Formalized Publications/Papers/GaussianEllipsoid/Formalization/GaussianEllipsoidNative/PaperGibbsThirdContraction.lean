import PaperGibbsThirdMass
import PaperThirdQuadraticBound
import PaperCavityContraction
noncomputable section
open BMQuadraticStein BMSmoothQuadraticComposition PaperGibbsThird PaperGibbsThirdTest
open PaperGibbsThirdMass PaperTensorMass PaperThirdQuadraticBound
open scoped BigOperators BoundedContinuousFunction
namespace PaperGibbsThirdContraction
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℕ}

def contraction (D : Data3 κ) (q : κ → MvPolynomial (Fin d) ℝ)
    (R : κ → Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c,
    boundedExpectation ((boundedThird D a b c).compContinuous (polynomialFamily q))
      (quadratic (R b * R a * R c))

/-- Actual Gibbs third-derivative contraction is controlled by the source's
C3 loss combination, with uniform dimension/candidate/shift dependence. -/
theorem contraction_le (D : Data3 κ)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (q : κ → MvPolynomial (Fin d) ℝ)
    (R : κ → Matrix (Fin d) (Fin d) ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hop : ∀ a, spectralNorm (R a) ≤ τ) (hfrob : ∀ a, frobeniusSq (R a) ≤ 1) :
    |contraction D q R| ≤ Real.sqrt 3 * τ * Real.exp (3 * D.beta) *
      (D.beta * ‖D.potentialThird‖ +
        6 * D.beta^2 * ‖D.potentialDeriv‖ * ‖D.potentialSecond‖ +
        6 * D.beta^3 * ‖D.potentialDeriv‖^3) := by
  have hbound (a b c : κ) :
      |boundedExpectation ((boundedThird D a b c).compContinuous (polynomialFamily q))
        (quadratic (R b * R a * R c))| ≤ Real.sqrt 3 * τ * ‖boundedThird D a b c‖ :=
    (bounded_triple_test_le (R b) (R a) (R c) _ hτ hτ1 (hop b) (hop a) (hfrob b) (hfrob c)).trans
      (mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_compContinuous_le _ _) (by positivity))
  calc
    _ ≤ ∑ a, ∑ b, ∑ c, |boundedExpectation
        ((boundedThird D a b c).compContinuous (polynomialFamily q))
        (quadratic (R b * R a * R c))| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro b _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, ∑ c, Real.sqrt 3 * τ * ‖boundedThird D a b c‖ :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        Finset.sum_le_sum fun c _ => hbound a b c
    _ = Real.sqrt 3 * τ * mass (fun a b c => boundedThird D a b c) := by
      simp only [mass, ← Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (boundedThird_mass_le D hunit)
        (show 0 ≤ Real.sqrt 3 * τ by positivity)
      simpa only [mul_assoc] using hh

/-- Source-normalized third remainder, with explicit universal constant and
literal 1/n. Telescoping n row replacements is still a separate obligation. -/
theorem normalized_contraction_le (D : Data3 κ)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (hβ : 0 < D.beta) (n : ℕ) (hn : 0 < n)
    (q : κ → MvPolynomial (Fin d) ℝ)
    (R : κ → Matrix (Fin d) (Fin d) ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hop : ∀ a, spectralNorm (R a) ≤ τ) (hfrob : ∀ a, frobeniusSq (R a) ≤ 1) :
    |(-(Real.sqrt 2 / (D.beta * (n : ℝ)))) * contraction D q R| ≤
      (6 * Real.sqrt 2 * Real.sqrt 3) * Real.exp (3 * D.beta) * τ / n *
        (‖D.potentialThird‖ + D.beta * ‖D.potentialDeriv‖ * ‖D.potentialSecond‖ +
          D.beta^2 * ‖D.potentialDeriv‖^3) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hbn : D.beta ≠ 0 := ne_of_gt hβ
  have hnn : (n : ℝ) ≠ 0 := ne_of_gt hn'
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2 / (D.beta * (n : ℝ)))]
  calc
    _ ≤ (Real.sqrt 2 / (D.beta * (n : ℝ))) *
        (Real.sqrt 3 * τ * Real.exp (3 * D.beta) *
          (D.beta * ‖D.potentialThird‖ +
            6 * D.beta^2 * ‖D.potentialDeriv‖ * ‖D.potentialSecond‖ +
            6 * D.beta^3 * ‖D.potentialDeriv‖^3)) :=
      mul_le_mul_of_nonneg_left (contraction_le D hunit q R hτ hτ1 hop hfrob) (by positivity)
    _ = (Real.sqrt 2 * Real.sqrt 3 * Real.exp (3 * D.beta) * τ / n) *
        (‖D.potentialThird‖ + 6*D.beta*‖D.potentialDeriv‖*‖D.potentialSecond‖ +
          6*D.beta^2*‖D.potentialDeriv‖^3) := by
      field_simp [hbn, hnn] <;> ring
    _ ≤ (Real.sqrt 2 * Real.sqrt 3 * Real.exp (3 * D.beta) * τ / n) *
        (6 * (‖D.potentialThird‖ + D.beta*‖D.potentialDeriv‖*‖D.potentialSecond‖ +
          D.beta^2*‖D.potentialDeriv‖^3)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact PaperCavityContraction.paper_scalar_mass_le hβ.le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

#print axioms contraction_le
#print axioms normalized_contraction_le
end PaperGibbsThirdContraction
