import GramSchmidtProjection
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Constructions.Pi

open InnerProductSpace

noncomputable section
open MeasureTheory Finset

namespace GaussianMixedNormHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual Gram-Schmidt residual is Borel measurable, including the singular
prefixes, where Lean's scalar division is totalized. -/
theorem measurable_gramSchmidt {r : ℕ} (j : Fin r) :
    Measurable (fun f : Fin r → E => gramSchmidt ℝ f j) := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hformula : (fun f : Fin r → E => gramSchmidt ℝ f j) =
        (fun f => f j - ∑ i ∈ Finset.Iio j,
          (inner (𝕜 := ℝ) (gramSchmidt ℝ f i) (f j) / ‖gramSchmidt ℝ f i‖ ^ 2) •
            gramSchmidt ℝ f i) := by
      funext f
      exact eq_sub_iff_add_eq.mpr (gramSchmidt_def'' ℝ f j).symm
    rw [hformula]
    apply (measurable_pi_apply j).sub
    apply Finset.measurable_sum
    intro i hi
    have hi' := ih i (Finset.mem_Iio.mp hi)
    exact ((hi'.inner (measurable_pi_apply j)).div (hi'.norm.pow_const 2)).smul hi'

/-- Borel measurability of the complete vector of squared GS lengths. -/
theorem measurable_gramSchmidt_norm_sq {r : ℕ} :
    Measurable (fun f : Fin r → E => fun j => ‖gramSchmidt ℝ f j‖ ^ 2) := by
  exact measurable_pi_iff.mpr fun j => (measurable_gramSchmidt j).norm.pow_const 2

/-- Appending a new row leaves every earlier prior span unchanged. -/
theorem priorSpan_snoc_castSucc [FiniteDimensional ℝ E] {r : ℕ}
    (f : Fin r → E) (x : E) (j : Fin r) :
    priorSpan (Fin.snoc f x) j.castSucc = priorSpan f j := by
  simp only [priorSpan_eq_span_image]
  congr 1
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i ≠ Fin.last r := by
      intro heq
      subst i
      exact (not_lt_of_ge (Fin.le_last _)) hi
    obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hin
    exact ⟨k, by simpa using hi, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, by simpa using hi, by simp⟩

/-- Prefix stability of actual Gram-Schmidt residuals, proved through the exact
orthogonal-projection characterization rather than assumed recursively. -/
theorem gramSchmidt_snoc_castSucc [FiniteDimensional ℝ E] {r : ℕ}
    (f : Fin r → E) (x : E) (j : Fin r) :
    gramSchmidt ℝ (Fin.snoc f x) j.castSucc = gramSchmidt ℝ f j := by
  rw [gramSchmidt_eq_sub_priorProjection, gramSchmidt_eq_sub_priorProjection,
    priorSpan_snoc_castSucc, Fin.snoc_castSucc]

/-- The final-row prior span is exactly the span of the existing rows. -/
theorem priorSpan_snoc_last [FiniteDimensional ℝ E] {r : ℕ}
    (f : Fin r → E) (x : E) :
    priorSpan (Fin.snoc f x) (Fin.last r) = Submodule.span ℝ (Set.range f) := by
  rw [priorSpan_eq_span_image]
  congr 1
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i ≠ Fin.last r := ne_of_lt hi
    obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hin
    exact ⟨k, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, by simp, by simp⟩

/-- The sequential Gram-Schmidt one-row squared-residual function. -/
def gramSchmidtStep (n : ℕ) (f : Fin n → E) (x : E) : ℝ :=
  ‖gramSchmidt ℝ (Fin.snoc f x) (Fin.last n)‖ ^ 2

/-- Joint measurability of the previous rows and current row. -/
theorem measurable_gramSchmidtStep (n : ℕ) :
    Measurable (Function.uncurry (gramSchmidtStep (E := E) n)) := by
  apply ((measurable_gramSchmidt (Fin.last n)).norm.pow_const 2).comp
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simpa [Function.comp_def] using (measurable_pi_apply j).comp measurable_fst

/-- Actual fibre residual formula used for the fixed-subspace Gaussian law. -/
theorem gramSchmidtStep_eq_projection [FiniteDimensional ℝ E]
    (n : ℕ) (f : Fin n → E) (x : E) :
    gramSchmidtStep n f x =
      ‖((Submodule.span ℝ (Set.range f))ᗮ).orthogonalProjection x‖ ^ 2 := by
  unfold gramSchmidtStep
  rw [gramSchmidt_eq_priorOrthogonalProjection, priorSpan_snoc_last, Fin.snoc_last]
  rfl

end GaussianMixedNormHelpers
