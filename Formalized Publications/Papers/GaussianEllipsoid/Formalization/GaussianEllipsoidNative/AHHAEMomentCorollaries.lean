import AHHPositiveMomentCorollaries

/-! Almost-everywhere versions: no hidden all-input bounds on an ambient law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace AHHBoundedPositiveMoments
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem moments_of_ae_bounds (F : Ω → ℝ) (hF : Measurable F) {B a : ℝ}
    (hB : 1 ≤ B) (hbound : ∀ᵐ w ∂P, 1 ≤ F w ∧ F w ≤ B) (ha : 0 < a)
    (hEnt : ∀ p : ℝ, powerEntropy P (fun w => Real.log (F w)) p ≤
      p^2/a * (∫ w, (F w)^(p-1) ∂P)) :
    (∀ q : ℝ, 1 ≤ q → (∫ w, (F w)^q ∂P)^(1/q) ≤
      (∫ w, F w ∂P) + (q-1)/a) ∧
    (∀ t : ℝ, 0 ≤ t → Real.log (∫ w, (F w / (∫ z, F z ∂P))^(-t) ∂P) ≤
      t*(t+1)/a) := by
  let G := fun w => max 1 (min B (F w))
  have hG : Measurable G := measurable_const.max (measurable_const.min hF)
  have hG1 (w : Ω) : 1 ≤ G w := le_max_left _ _
  have hGB (w : Ω) : G w ≤ B := max_le hB (min_le_left _ _)
  have heq : G =ᵐ[P] F := hbound.mono fun w hw => by
    dsimp [G]
    rw [min_eq_right hw.2, max_eq_right hw.1]
  have hmean : (∫ w, G w ∂P) = ∫ w, F w ∂P := integral_congr_ae heq
  have hpow (p : ℝ) : (∫ w, (G w)^p ∂P) = ∫ w, (F w)^p ∂P :=
    integral_congr_ae (heq.mono fun w hw => by dsimp only; rw [hw])
  have hlogeq : (fun w => Real.log (G w)) =ᵐ[P] (fun w => Real.log (F w)) :=
    heq.mono fun w hw => congrArg Real.log hw
  have hEntG (p : ℝ) : powerEntropy P (fun w => Real.log (G w)) p ≤
      p^2/a * (∫ w, (G w)^(p-1) ∂P) := by
    rw [powerEntropy_congr P hlogeq, hpow]
    exact hEnt p
  constructor
  · intro q hq
    simpa only [hpow, hmean] using positive_moment_le P G hG hG1 hGB ha hEntG hq
  · intro t ht
    have hn : (∫ w, (G w / (∫ z, G z ∂P))^(-t) ∂P) =
        ∫ w, (F w / (∫ z, F z ∂P))^(-t) ∂P := by
      rw [hmean]
      exact integral_congr_ae (heq.mono fun w hw => by dsimp only; rw [hw])
    simpa only [hn] using negative_moment_le P G hG hG1 hGB ha hEntG ht

#print axioms moments_of_ae_bounds
end AHHBoundedPositiveMoments
