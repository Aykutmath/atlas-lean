import PaperProjectionPolarBound
import SpectralFrobenius
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
open GaussianEllipsoid
open scoped Matrix.Norms.L2Operator MatrixOrder InnerProductSpace
namespace GaussianEllipsoid.PaperGrassmannRotation
open PaperProjectionPolarAlgebra

/-- Sharp near-identity rotation between close orthogonal projections.
No dimension equality is assumed: closeness below one already forces it. -/
theorem exists_rotation {d : ℕ} [NeZero d] (E F : Submodule ℝ (Euclid d))
    (hEF : ‖E.starProjection-F.starProjection‖ < 1) :
    ∃ O : Euclid d ≃ₗᵢ[ℝ] Euclid d,
      E.map O.toLinearEquiv.toLinearMap=F ∧
      ‖O.toLinearIsometry.toContinuousLinearMap-1‖ ≤
        Real.sqrt 2*‖E.starProjection-F.starProjection‖ := by
  let e := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
  let P := e.symm E.starProjection
  let Q := e.symm F.starProjection
  have hP : IsStarProjection P := (isStarProjection_starProjection (U := E)).map e.symm
  have hQ : IsStarProjection Q := (isStarProjection_starProjection (U := F)).map e.symm
  have hnorm : ‖P-Q‖=‖E.starProjection-F.starProjection‖ := by
    rw [Matrix.cstar_norm_def,map_sub]
    simp only [P,Q,e,StarAlgEquiv.apply_symm_apply]
  have hδ : ‖P-Q‖<1 := hnorm.trans_lt hEF
  let T := e (polar P Q)
  have hTT : T.adjoint*T=1 := by
    have h := congrArg e (polar_star_mul P Q hP hQ hδ)
    simpa only [map_mul,map_star,map_one,T,ContinuousLinearMap.star_eq_adjoint] using h
  have hn (x : Euclid d) : ‖T x‖=‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq,← ContinuousLinearMap.adjoint_inner_right]
    have he : T.adjoint (T x)=x := congrArg (fun f : Euclid d →L[ℝ] Euclid d => f x) hTT
    rw [he,real_inner_self_eq_norm_sq]
  let L : Euclid d →ₗᵢ[ℝ] Euclid d := ⟨T.toLinearMap,hn⟩
  let O := LinearIsometryEquiv.ofSurjective L (LinearMap.surjective_of_injective L.injective)
  have hcomm (x : Euclid d) : T (E.starProjection x)=F.starProjection (T x) := by
    have h := congrArg e (polar_intertwine P Q hP hQ)
    have he : T*E.starProjection=F.starProjection*T := by
      simpa only [map_mul,P,Q,e,StarAlgEquiv.apply_symm_apply,T] using h
    exact congrArg (fun f : Euclid d →L[ℝ] Euclid d => f x) he
  refine ⟨O,?_,?_⟩
  · apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      apply F.starProjection_eq_self_iff.mp
      change F.starProjection (T x)=T x
      rw [← hcomm,E.starProjection_eq_self_iff.mpr hx]
    · intro y hy
      obtain ⟨x,hx⟩ := O.surjective y
      refine ⟨x,?_,hx⟩
      apply E.starProjection_eq_self_iff.mp
      apply L.injective
      change T (E.starProjection x)=T x
      rw [hcomm]
      change F.starProjection (O x)=O x
      rw [hx,F.starProjection_eq_self_iff.mpr hy]
  · have h := polar_norm_sub_one_le P Q hP hQ hδ
    rw [hnorm,Matrix.cstar_norm_def,map_sub,map_one] at h
    exact h

/-- Literal near-identity rotation clause of the paper Grassmann-net lemma. -/
theorem paper_rotation {d : ℕ} (E F : Submodule ℝ (Euclid d))
    (ζ : ℝ) (hζ : 0 < ζ) (hζhalf : ζ < 1/2)
    (hEF : ‖E.starProjection-F.starProjection‖ ≤ ζ) :
    ∃ O : Euclid d ≃ₗᵢ[ℝ] Euclid d,
      E.map O.toLinearEquiv.toLinearMap=F ∧
      ‖O.toLinearIsometry.toContinuousLinearMap-1‖ ≤ Real.sqrt 2*ζ := by
  by_cases hd : d=0
  · subst d
    refine ⟨LinearIsometryEquiv.refl ℝ _,?_,?_⟩
    · exact Subsingleton.elim _ _
    · have hz : 0 ≤ Real.sqrt 2*ζ := mul_nonneg (Real.sqrt_nonneg _) hζ.le
      simpa using hz
  · letI : NeZero d := ⟨hd⟩
    obtain ⟨O,hmap,hbound⟩ := exists_rotation E F (lt_of_le_of_lt hEF (by linarith))
    exact ⟨O,hmap,hbound.trans (mul_le_mul_of_nonneg_left hEF (Real.sqrt_nonneg _))⟩

#print axioms paper_rotation
#print axioms exists_rotation
end GaussianEllipsoid.PaperGrassmannRotation
