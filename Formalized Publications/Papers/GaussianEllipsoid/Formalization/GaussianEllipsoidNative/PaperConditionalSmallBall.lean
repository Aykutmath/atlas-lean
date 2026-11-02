import PaperSmallBallAdapter

/-! Reconstructed source, 2026-10-03. This is new text, not recovered original bytes. -/
noncomputable section
open MeasureTheory GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators
namespace GaussianEllipsoid.SmallBall

/-- Joint measurability for arbitrary measurable, random coefficients. -/
theorem measurable_random_bilinearFlat {Ω : Type*} [MeasurableSpace Ω]
    (r n : ℕ) (z : Ω → Fin n → ℝ) (hz : Measurable z) :
    Measurable (fun p : Ω × BilinearSample r n => bilinearFlat r n (z p.1) p.2) := by
  let f : Ω × BilinearSample r n → (Fin r × Fin r → ℝ) :=
    fun p pq => (Real.sqrt (r : ℝ))⁻¹ *
      ∑ i, z p.1 i * p.2.1 i pq.1 * p.2.2 (i, pq.2)
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro pq
    unfold f
    fun_prop
  have hm := (MeasurableEquiv.toLp 2 ((Fin r × Fin r) → ℝ)).measurable.comp hf
  have heq : (fun p : Ω × BilinearSample r n => bilinearFlat r n (z p.1) p.2) =
      (MeasurableEquiv.toLp 2 ((Fin r × Fin r) → ℝ)) ∘ f := by
    funext p
    ext pq
    exact matrixCLM_bilinearDriver_apply _ (z p.1) p.2.1 p.2.2 pq.1 pq.2
  rw [heq]
  exact hm

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.measurable_random_bilinearFlat
