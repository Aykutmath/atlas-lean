import Section_10_Zonoid.Cor101.ProjectionContinuity
import Section_10_Zonoid.Cor101.Translation

/-! Closedness and passage from finite zonotopes to zonoids. -/
open MeasureTheory
noncomputable section
namespace Cor101

theorem projectionInequality_iff_toReal {d : Nat} (K : ConvexBody (Space d)) :
    ProjectionInequality K ↔
      (fullVolume K).toReal * (lineVolume K).toReal ^ (d - 1) ≤
        ∏ j : Fin d, (planeVolume K j).toReal := by
  unfold ProjectionInequality
  rw [← ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (fullVolume_ne_top K) (ENNReal.pow_ne_top (lineVolume_ne_top K)))
    (ENNReal.prod_ne_top (fun j _ => planeVolume_ne_top K j))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_prod]

theorem isClosed_projectionInequality (d : Nat) :
    IsClosed {K : ConvexBody (Space d) | ProjectionInequality K} := by
  simp_rw [projectionInequality_iff_toReal]
  have hf : Continuous (fun K : ConvexBody (Space d) => (fullVolume K).toReal) := by
    exact continuous_iff_continuousAt.mpr (fun K =>
      (ENNReal.continuousAt_toReal (fullVolume_ne_top K)).comp
        (fullVolume_continuous d).continuousAt)
  have hl : Continuous (fun K : ConvexBody (Space d) => (lineVolume K).toReal) := by
    exact continuous_iff_continuousAt.mpr (fun K =>
      (ENNReal.continuousAt_toReal (lineVolume_ne_top K)).comp
        (lineVolume_continuous d).continuousAt)
  have hp : ∀ j : Fin d, Continuous (fun K : ConvexBody (Space d) =>
      (planeVolume K j).toReal) := by
    intro j
    exact ENNReal.continuousOn_toReal.comp_continuous (planeVolume_continuous d j)
      (fun K => planeVolume_ne_top K j)
  exact isClosed_le (hf.mul (hl.pow _)) (continuous_finsetProd _ (fun j _ => hp j))

/-- The geometric inequality extends from finite zonotopes to every zonoid.
The sole input is its validity on finite zonotopes, not any continuity hypothesis. -/
theorem zonoid_projection_of_zonotope {d : Nat}
    (hfinite : ∀ Z : ConvexBody (Space d), IsZonotope Z → ProjectionInequality Z)
    (K : ConvexBody (Space d)) (hK : IsZonoid K) : ProjectionInequality K := by
  have hsub : {Z : ConvexBody (Space d) | IsZonotope Z} ⊆
      {Z : ConvexBody (Space d) | ProjectionInequality Z} :=
    fun Z hZ => hfinite Z hZ
  exact (closure_minimal hsub (isClosed_projectionInequality d)) hK

/-- Translation invariance extends a generator-family theorem to all translated zonotopes. -/
theorem zonotope_projection_of_generators {d : Nat}
    (hgen : ∀ (N : Nat) (v : Fin N → Space d), ProjectionInequality (zonotopeBody v))
    (K : ConvexBody (Space d)) (hK : IsZonotope K) : ProjectionInequality K := by
  obtain ⟨N, a, v, hv⟩ := hK
  have heq : K = translate a (zonotopeBody v) := by
    apply SetLike.coe_injective
    exact hv
  rw [heq, projectionInequality_translate_iff]
  exact hgen N v

end Cor101
