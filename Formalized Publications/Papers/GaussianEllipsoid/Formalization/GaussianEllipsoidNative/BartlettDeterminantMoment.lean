import BartlettJointLaw
import GammaExtendedMoment

open InnerProductSpace

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Module Finset
namespace GaussianMixedNormHelpers

/-- Reversing coordinates reverses the factors of a finite product measure. -/
theorem pi_map_finReverse {Y : Type*} [MeasurableSpace Y] {r : ℕ}
    (μ : Fin r → Measure Y) [∀ i, SigmaFinite (μ i)] :
    Measure.map (fun x : Fin r → Y => fun i : Fin r => x i.rev) (Measure.pi μ) =
      Measure.pi (fun i : Fin r => μ i.rev) := by
  have h := Measure.pi_map_piCongrLeft Fin.revPerm (fun i : Fin r => μ i.rev)
  simpa [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Fin.revPerm] using! h

/-- Reverse residual order exactly matches the gamma law used by the inverse-
moment module, for a matrix with r rows and r+2s columns. -/
theorem gaussianRows_map_revGramSchmidt (r s : ℕ) :
    Measure.map (fun f : Fin r → EuclideanSpace ℝ (Fin (r + 2 * s)) =>
      fun j : Fin r => ‖gramSchmidt ℝ f j.rev‖ ^ 2)
      (Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin (r + 2 * s)))) =
        bartlettGammaLaw r s := by
  let μ : Fin r → Measure ℝ := fun j : Fin r =>
    gammaMeasure (((r + 2 * s - j.val : ℕ) : ℝ) / 2) (1 / 2)
  letI (j : Fin r) : SigmaFinite (μ j) := by
    dsimp [μ]
    unfold gammaMeasure gammaPDF
    infer_instance
  have hm : Measurable (fun x : Fin r → ℝ => fun j : Fin r => x j.rev) :=
    measurable_pi_lambda _ (fun j : Fin r => measurable_pi_apply j.rev)
  have heq : (fun f : Fin r → EuclideanSpace ℝ (Fin (r + 2 * s)) =>
      fun j : Fin r => ‖gramSchmidt ℝ f j.rev‖ ^ 2) =
      (fun x : Fin r → ℝ => fun j : Fin r => x j.rev) ∘
        (fun f : Fin r → EuclideanSpace ℝ (Fin (r + 2 * s)) =>
          fun j : Fin r => ‖gramSchmidt ℝ f j‖ ^ 2) := rfl
  rw [heq, ← Measure.map_map hm measurable_gramSchmidt_norm_sq,
    gaussianRows_map_gramSchmidt_norm_sq r (r + 2 * s) (by omega)]
  change Measure.map (fun x : Fin r → ℝ => fun j : Fin r => x j.rev) (Measure.pi μ) = _
  rw [pi_map_finReverse, bartlettGammaLaw]
  congr 1
  funext j
  dsimp [μ]
  have hnat : r + 2 * s - j.rev.val = 2 * s + j.val + 1 := by
    simp only [Fin.val_rev]
    omega
  simp only [Fin.val_rev] at hnat
  rw [hnat]
  congr 1
  push_cast
  ring

/-- The reversed squared-residual product is exactly the Gram determinant. -/
theorem prod_rev_gramSchmidt_eq_gramDet {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {r : ℕ} (f : Fin r → E) :
    (∏ j : Fin r, ‖gramSchmidt ℝ f j.rev‖ ^ 2) = (realGramMatrix f).det := by
  rw [det_realGramMatrix_eq_prod_gramSchmidt_norm_sq]
  simpa using Equiv.prod_comp Fin.revPerm (fun j : Fin r => ‖gramSchmidt ℝ f j‖ ^ 2)

/-- Scaled extended inverse determinant moment under the actual Gaussian row law.
Singular matrices contribute infinity, as in the paper, rather than Lean's real
inverse-at-zero convention. The bound is unconditional. -/
theorem gaussianRows_scaled_extended_inverse_det_moment_le (r s : ℕ) (hr : 0 < r) :
    (∫⁻ f : Fin r → EuclideanSpace ℝ (Fin (r + 2 * s)),
      ((ENNReal.ofReal (((2 * (r : ℝ)) ^ r)⁻¹ * (realGramMatrix f).det)) ^ s)⁻¹
        ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin (r + 2 * s)))) ≤
      ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s)) := by
  have hm : Measurable (fun f : Fin r → EuclideanSpace ℝ (Fin (r + 2 * s)) =>
      fun j : Fin r => ‖gramSchmidt ℝ f j.rev‖ ^ 2) :=
    measurable_pi_iff.mpr (fun j : Fin r => (measurable_gramSchmidt j.rev).norm.pow_const 2)
  have hi := lintegral_map
    (μ := Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin (r + 2 * s))))
    (f := fun x : Fin r → ℝ => ((ENNReal.ofReal (((2 * (r : ℝ)) ^ r)⁻¹ * ∏ j : Fin r, x j)) ^ s)⁻¹)
    (by fun_prop) hm
  rw [gaussianRows_map_revGramSchmidt] at hi
  simp only [prod_rev_gramSchmidt_eq_gramDet] at hi
  rw [← hi]
  exact bartlettGammaLaw_scaled_extended_inverse_moment_le r s hr

end GaussianMixedNormHelpers
