import PaperThirdMassAlgebra
import PaperCavityPrior
noncomputable section
open BMFiniteGibbsTest BMFiniteGibbsHessian PaperGibbsThird PaperGibbsThirdTest
open PaperCavityPrior PaperTensorMass PaperThirdMassAlgebra
open scoped BigOperators BoundedContinuousFunction
namespace PaperGibbsThirdMass
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The full replica identity holds in bounded continuous functions, so taking
sup norms after prior domination is legitimate. -/
theorem boundedThird_eq_replicaTensor (D : Data3 κ) :
    (fun a b c => boundedThird D a b c) =
      replicaTensor D.beta (boundedProbability D.toData) (first D.toData)
        (second D.toData2) (PaperGibbsThirdTest.third D) := by
  ext a b c y
  rw [boundedThird_apply, PaperGibbsThird.third_eq_replicaThird]
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c
  all_goals simp [replicaTensor, diagonal, pairAB, pairAC, pairBC,
    boundedProbability, first, second, PaperGibbsThirdTest.third, coordinate,
    replicaThird, hab, hac, hbc]
  all_goals ring <;> simp_all [eq_comm]

/-- Sum of sup norms of Gibbs probabilities retains the fixed prior before
supremum; this is the step that prevents a candidate-count loss. -/
theorem probability_priorMass_le (D : Data κ)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1) :
    priorMass (boundedProbability D) ≤ Real.exp D.beta := by
  have hb (a : κ) : ‖boundedProbability D a‖ ≤ Real.exp D.beta * D.weight a := by
    apply (BoundedContinuousFunction.norm_le
      (mul_nonneg (Real.exp_nonneg _) (D.weight_nonneg a))).2
    intro y
    change ‖probability D y a‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (probability_nonneg D y a)]
    exact probability_le_exp_prior D hunit y a
  calc
    _ ≤ ∑ a, Real.exp D.beta * D.weight a := Finset.sum_le_sum fun a _ => hb a
    _ = _ := by rw [← Finset.mul_sum, D.weight_sum, mul_one]

/-- Actual Gibbs third derivative has the exact paper scalar mass 1,6,6 and
exp(3β), with no cardinality or dimension factor. This is for log partition;
the cavity free energy multiplies by −1/(β n). -/
theorem boundedThird_mass_le (D : Data3 κ)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1) :
    mass (fun a b c => boundedThird D a b c) ≤ Real.exp (3 * D.beta) *
      (D.beta * ‖D.potentialThird‖ +
        6 * D.beta^2 * ‖D.potentialDeriv‖ * ‖D.potentialSecond‖ +
        6 * D.beta^3 * ‖D.potentialDeriv‖^3) := by
  rw [boundedThird_eq_replicaTensor]
  let P := priorMass (boundedProbability D.toData)
  have hP0 : 0 ≤ P := priorMass_nonneg _
  have hP : P ≤ Real.exp D.beta := probability_priorMass_le D.toData hunit
  have hβ := D.beta_nonneg
  have hP1 : P ≤ Real.exp (3 * D.beta) := hP.trans (Real.exp_le_exp.mpr (by linarith))
  have hP2 : P^2 ≤ Real.exp (3 * D.beta) := by
    calc
      _ ≤ (Real.exp D.beta)^2 := pow_le_pow_left₀ hP0 hP 2
      _ = Real.exp (2 * D.beta) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hP3 : P^3 ≤ Real.exp (3 * D.beta) := by
    calc
      _ ≤ (Real.exp D.beta)^3 := pow_le_pow_left₀ hP0 hP 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h := replicaTensor_mass_le D.beta (boundedProbability D.toData)
    (first D.toData) (second D.toData2) (PaperGibbsThirdTest.third D)
    hβ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (fun a => BoundedContinuousFunction.norm_compContinuous_le _ _)
    (fun a => BoundedContinuousFunction.norm_compContinuous_le _ _)
    (fun a => BoundedContinuousFunction.norm_compContinuous_le _ _)
  change _ ≤ D.beta * ‖D.potentialThird‖ * P +
    3 * D.beta^2 * ‖D.potentialDeriv‖ * ‖D.potentialSecond‖ * (P+P^2) +
    D.beta^3 * ‖D.potentialDeriv‖^3 * (P+3*P^2+2*P^3) at h
  have h1 := mul_le_mul_of_nonneg_left hP1
    (mul_nonneg hβ (norm_nonneg D.potentialThird))
  have h2 := mul_le_mul_of_nonneg_left (show P+P^2 ≤ 2*Real.exp (3*D.beta) by linarith [hP1,hP2])
    (show 0 ≤ 3*D.beta^2*‖D.potentialDeriv‖*‖D.potentialSecond‖ by positivity)
  have h3 := mul_le_mul_of_nonneg_left
    (show P+3*P^2+2*P^3 ≤ 6*Real.exp (3*D.beta) by linarith [hP1,hP2,hP3])
    (show 0 ≤ D.beta^3*‖D.potentialDeriv‖^3 by positivity)
  nlinarith

#print axioms boundedThird_mass_le
end PaperGibbsThirdMass
