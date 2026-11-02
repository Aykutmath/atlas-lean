import GramSchmidtDeterminant

open InnerProductSpace

noncomputable section
open Finset
namespace GaussianMixedNormHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The prior span can equally be described as the image of the strict prefix. -/
theorem priorSpan_eq_span_image {r : ℕ} (f : Fin r → E) (j : Fin r) :
    priorSpan f j = Submodule.span ℝ (f '' Set.Iio j) := by
  unfold priorSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.property, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

/-- Every earlier Gram–Schmidt residual lies in the current prior span. -/
theorem gramSchmidt_mem_priorSpan {r : ℕ} (f : Fin r → E)
    {i j : Fin r} (hij : i < j) : gramSchmidt ℝ f i ∈ priorSpan f j := by
  rw [priorSpan_eq_span_image]
  exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iio.mpr hij))
    (gramSchmidt_mem_span ℝ f (le_refl i))

/-- The current Gram–Schmidt residual is orthogonal to the full prior span. -/
theorem gramSchmidt_mem_priorSpan_orthogonal {r : ℕ} (f : Fin r → E) (j : Fin r) :
    gramSchmidt ℝ f j ∈ (priorSpan f j)ᗮ := by
  have hspan : priorSpan f j ≤ LinearMap.ker (innerSL ℝ (gramSchmidt ℝ f j)).toLinearMap := by
    unfold priorSpan
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change inner (𝕜 := ℝ) (gramSchmidt ℝ f j) (f i) = 0
    exact gramSchmidt_inv_triangular ℝ f i.property
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro x hx
  exact hspan hx

/-- The part subtracted by Gram–Schmidt belongs to the prior span. -/
theorem sub_gramSchmidt_mem_priorSpan {r : ℕ} (f : Fin r → E) (j : Fin r) :
    f j - gramSchmidt ℝ f j ∈ priorSpan f j := by
  have hcorr : f j - gramSchmidt ℝ f j =
      ∑ i ∈ Finset.Iio j,
        (inner (𝕜 := ℝ) (gramSchmidt ℝ f i) (f j) / ‖gramSchmidt ℝ f i‖ ^ 2) •
          gramSchmidt ℝ f i := by
    apply sub_eq_iff_eq_add.mpr
    simpa [add_comm] using gramSchmidt_def'' ℝ f j
  rw [hcorr]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (gramSchmidt_mem_priorSpan f (Finset.mem_Iio.mp hi))

/-- Exact bridge from recursive Gram–Schmidt to the prior-span projection. -/
theorem gramSchmidt_eq_sub_priorProjection [FiniteDimensional ℝ E]
    {r : ℕ} (f : Fin r → E) (j : Fin r) :
    gramSchmidt ℝ f j = f j - (priorSpan f j).orthogonalProjection (f j) := by
  have hp : ((priorSpan f j).orthogonalProjection (f j) : E) =
      f j - gramSchmidt ℝ f j := by
    change (priorSpan f j).starProjection (f j) = _
    apply Submodule.eq_starProjection_of_mem_orthogonal
      (sub_gramSchmidt_mem_priorSpan f j)
    simpa only [sub_sub_cancel] using gramSchmidt_mem_priorSpan_orthogonal f j
  rw [hp]
  abel

/-- The residual is precisely the orthogonal-complement projection used in
one-row Gaussian rotation arguments. -/
theorem gramSchmidt_eq_priorOrthogonalProjection [FiniteDimensional ℝ E]
    {r : ℕ} (f : Fin r → E) (j : Fin r) :
    gramSchmidt ℝ f j = ((priorSpan f j)ᗮ.orthogonalProjection (f j) : E) := by
  change gramSchmidt ℝ f j = (priorSpan f j)ᗮ.starProjection (f j)
  rw [Submodule.starProjection_orthogonal_val]
  exact gramSchmidt_eq_sub_priorProjection f j

end GaussianMixedNormHelpers
