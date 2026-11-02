import BMGordonFiniteCoordinates
import BMGordonFiniteAffine

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid BMGeometry BMSaddle BMGordon
namespace UCEscape

/-- Gordon's genuine finite escape comparison. The minimization is over matrices,
not measurement directions. No conditioning-number restriction is imposed. -/
theorem finite_escape_comparison {n d : ℕ}
    (I J : Type) [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (S : I → HMat d) (u : I → J → Euclid n)
    (hS : ∀ i, ‖S i‖ = 1) (hu : ∀ i j, ‖u i j‖ = 1) :
    (∫ ω, finiteValue (fun i j ω => ⟪auxiliaryCoefficient (u i j) (S i),ω⟫_ℝ) ω ∂law n d) ≤
      ∫ ω, finiteValue (fun i j ω => ⟪primaryCoefficient (u i j) (S i),ω⟫_ℝ) ω ∂law n d := by
  classical
  let A : I × J → Space n d := fun a => auxiliaryCoefficient (u a.1 a.2) (S a.1)
  let B : I × J → Space n d := fun a => primaryCoefficient (u a.1 a.2) (S a.1)
  have hf := BMGordonFiniteAffine.minMax_expectation_le_linear
    (fun a => flatCoefficient (A a)) (fun a => flatCoefficient (B a)) (fun _ => 0)
  have hsame : ∀ a b : I × J, a.1 = b.1 →
      (∑ k, flatCoefficient (A a) k * flatCoefficient (A b) k) =
        ∑ k, flatCoefficient (B a) k * flatCoefficient (B b) k := by
    intro a b hab
    rw [flatCoefficient_inner, flatCoefficient_inner]
    dsimp [A, B]
    rw [auxiliaryCoefficient_inner, primaryCoefficient_inner, hab,
      real_inner_self_eq_norm_sq, hS]
    ring
  have hcov : ∀ a b : I × J,
      (∑ k, flatCoefficient (A a) k * flatCoefficient (A b) k) ≤
        ∑ k, flatCoefficient (B a) k * flatCoefficient (B b) k := by
    intro a b
    rw [flatCoefficient_inner, flatCoefficient_inner]
    dsimp [A, B]
    rw [auxiliaryCoefficient_inner, primaryCoefficient_inner]
    have hs := real_inner_le_norm (S a.1) (S b.1)
    have hv := real_inner_le_norm (u a.1 a.2) (u b.1 b.2)
    simp only [hS, hu, one_mul] at hs hv
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hv)]
  have ha := finite_integral_eq_flat A (fun _ => 0)
  have hb := finite_integral_eq_flat B (fun _ => 0)
  simpa only [A, B, add_zero] using ha.trans_le ((hf hsame hcov).trans_eq hb.symm)

#print axioms finite_escape_comparison
end UCEscape
