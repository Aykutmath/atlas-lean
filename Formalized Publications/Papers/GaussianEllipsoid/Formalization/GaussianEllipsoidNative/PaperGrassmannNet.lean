import UCFrameConjugation
import PolarDuality

noncomputable section
open GaussianEllipsoid
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.UCFrameGeometry

theorem frobeniusOperator_norm_le {d j : ℕ} (A : FrobeniusMatrix d j) :
    ‖frobeniusOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have he : frobeniusOperator A x = ∑ i, x i • A i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin j) ℝ).sum_repr x]
    simp only [map_sum,map_smul,frobeniusOperator_basis,EuclideanSpace.basisFun_repr]
  rw [he]
  apply (norm_sum_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R:=ℝ) Finset.univ
    (fun i => |x i|) (fun i => ‖A i‖)
  have hx : ∑ i, |x i|^2 = ‖x‖^2 := by simpa [Real.norm_eq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin j => ℝ) x).symm
  have hA : ∑ i, ‖A i‖^2 = ‖A‖^2 := (PiLp.norm_sq_eq_of_L2 (fun _ : Fin j => Euclid d) A).symm
  rw [hx,hA] at h
  apply (sq_le_sq₀ (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  nlinarith only [h]

@[simp] theorem frobeniusOperator_sub {d j : ℕ} (A B : FrobeniusMatrix d j) :
    frobeniusOperator (A-B)=frobeniusOperator A-frobeniusOperator B := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin j) ℝ).toBasis.ext
  intro i
  change frobeniusOperator (A-B) ((EuclideanSpace.basisFun (Fin j) ℝ) i) = _
  rw [frobeniusOperator_basis]
  change (A-B) i = frobeniusOperator A ((EuclideanSpace.basisFun (Fin j) ℝ) i)-frobeniusOperator B ((EuclideanSpace.basisFun (Fin j) ℝ) i)
  rw [frobeniusOperator_basis,frobeniusOperator_basis]
  rfl

def frameProjector {d j : ℕ} (U : FrobeniusMatrix d j) : Euclid d →L[ℝ] Euclid d :=
  frobeniusOperator U ∘L (frobeniusOperator U).adjoint

theorem frameProjector_distance {d j : ℕ} (U V : FrobeniusMatrix d j)
    (hU : IsFrame U) (hV : IsFrame V) :
    ‖frameProjector U-frameProjector V‖ ≤ 2*‖U-V‖ := by
  have hUn : ‖frobeniusOperator U‖ ≤ 1 := by
    rw [← frameLinearIsometry_toContinuousLinearMap U hU]
    exact (frameLinearIsometry U hU).norm_toContinuousLinearMap_le
  have hVn : ‖frobeniusOperator V‖ ≤ 1 := by
    rw [← frameLinearIsometry_toContinuousLinearMap V hV]
    exact (frameLinearIsometry V hV).norm_toContinuousLinearMap_le
  have he : frameProjector U-frameProjector V =
      (frobeniusOperator U-frobeniusOperator V) ∘L (frobeniusOperator U).adjoint +
      frobeniusOperator V ∘L (frobeniusOperator U-frobeniusOperator V).adjoint := by
    simp [frameProjector,ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub,map_sub]
  rw [he]
  have h1 := ContinuousLinearMap.opNorm_comp_le (frobeniusOperator U-frobeniusOperator V) (frobeniusOperator U).adjoint
  have h2 := ContinuousLinearMap.opNorm_comp_le (frobeniusOperator V) (frobeniusOperator U-frobeniusOperator V).adjoint
  simp only [LinearIsometryEquiv.norm_map] at h1 h2
  have hab := frobeniusOperator_norm_le (U-V)
  rw [frobeniusOperator_sub] at hab
  have hb1 := mul_le_mul_of_nonneg_left hUn (norm_nonneg (frobeniusOperator U-frobeniusOperator V))
  have hb2 := mul_le_mul_of_nonneg_right hVn (norm_nonneg (frobeniusOperator U-frobeniusOperator V))
  have hn := norm_add_le ((frobeniusOperator U-frobeniusOperator V) ∘L (frobeniusOperator U).adjoint) (frobeniusOperator V ∘L (frobeniusOperator U-frobeniusOperator V).adjoint)
  nlinarith
theorem exists_exact_projection_frame_net (d j : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ N : Finset (FrobeniusMatrix d j),
      (∀ U ∈ N, IsFrame U) ∧
      (N.card:ℝ) ≤ (1+4*Real.sqrt (j:ℝ)/ζ)^(d*j) ∧
      ∀ U : FrobeniusMatrix d j, IsFrame U → ∃ V ∈ N,
        ‖frameProjector U-frameProjector V‖ < ζ := by
  obtain ⟨N,hN,hcard,hcover⟩ := exists_internal_frame_net d j (half_pos hζ)
  refine ⟨N,hN,?_,?_⟩
  · convert hcard using 1 <;> congr 1 <;> ring
  · intro U hU
    obtain ⟨V,hV,hclose⟩ := hcover U hU
    exact ⟨V,hV,(frameProjector_distance U V hU (hN V hV)).trans_lt (by linarith)⟩

def frameSubspace {d j : ℕ} (U : FrobeniusMatrix d j) : Submodule ℝ (Euclid d) :=
  LinearMap.range (frobeniusOperator U).toLinearMap

theorem frameProjector_eq_starProjection {d j : ℕ} (U : FrobeniusMatrix d j)
    (hU : IsFrame U) : frameProjector U = (frameSubspace U).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨(frobeniusOperator U).adjoint x,rfl⟩
  · rintro w ⟨z,rfl⟩
    have hid : (frobeniusOperator U).adjoint ∘L frobeniusOperator U = ContinuousLinearMap.id ℝ _ := by
      rw [← frameLinearIsometry_toContinuousLinearMap U hU]
      exact (frameLinearIsometry U hU).adjoint_comp_self
    have hx : (frobeniusOperator U).adjoint (frobeniusOperator U z)=z := by
      exact congrArg (fun T : Euclid j →L[ℝ] Euclid j => T z) hid
    simp only [inner_sub_left,frameProjector,ContinuousLinearMap.comp_apply]
    change ⟪x, frobeniusOperator U z⟫_ℝ - ⟪frobeniusOperator U ((frobeniusOperator U).adjoint x), frobeniusOperator U z⟫_ℝ = 0
    rw [← ContinuousLinearMap.adjoint_inner_right, hx, ContinuousLinearMap.adjoint_inner_left]
    ring

theorem frameSubspace_finrank {d j : ℕ} (U : FrobeniusMatrix d j) (hU : IsFrame U) :
    Module.finrank ℝ (frameSubspace U)=j := by
  have hinj : Function.Injective (frobeniusOperator U).toLinearMap := (frameLinearIsometry U hU).injective
  have h := LinearMap.finrank_range_of_inj (f := (frobeniusOperator U).toLinearMap) hinj
  exact h.trans (by simp [Euclid])
theorem exists_frame_of_subspace {d j : ℕ} (E : Submodule ℝ (Euclid d))
    (hE : Module.finrank ℝ E = j) :
    ∃ U : FrobeniusMatrix d j, IsFrame U ∧ frameSubspace U = E := by
  let b : OrthonormalBasis (Fin j) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hE)
  let F : Euclid j →ₗᵢ[ℝ] Euclid d := E.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let U := operatorFrobenius F.toContinuousLinearMap
  refine ⟨U,linearIsometry_columns_isFrame F,?_⟩
  unfold frameSubspace U
  rw [frobeniusOperator_operatorFrobenius]
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    exact (b.repr.symm y).property
  · intro x hx
    refine ⟨b.repr ⟨x,hx⟩,?_⟩
    change ((b.repr.symm (b.repr ⟨x,hx⟩) : E) : Euclid d)=x
    simp

/-- Exact Grassmann projection-distance net with the source cardinality bound. -/
theorem paper_grassmann_projection_net (d j : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ N : Finset (Submodule ℝ (Euclid d)),
      (∀ E ∈ N, Module.finrank ℝ E = j) ∧
      (N.card:ℝ) ≤ (1+4*Real.sqrt (j:ℝ)/ζ)^(d*j) ∧
      ∀ E : Submodule ℝ (Euclid d), Module.finrank ℝ E = j → ∃ F ∈ N,
        ‖E.starProjection-F.starProjection‖ < ζ := by
  classical
  obtain ⟨N,hN,hcard,hcover⟩ := exists_exact_projection_frame_net d j hζ
  refine ⟨N.image frameSubspace,?_,?_,?_⟩
  · intro E hE
    obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hE
    exact frameSubspace_finrank U (hN U hU)
  · exact (Nat.cast_le.mpr (Finset.card_image_le)).trans hcard
  · intro E hE
    obtain ⟨U,hU,hUE⟩ := exists_frame_of_subspace E hE
    obtain ⟨V,hV,hUV⟩ := hcover U hU
    refine ⟨frameSubspace V,Finset.mem_image.mpr ⟨V,hV,rfl⟩,?_⟩
    rw [frameProjector_eq_starProjection U hU,frameProjector_eq_starProjection V (hN V hV),hUE] at hUV
    exact hUV

/-- The zero-dimensional Grassmannian is the singleton zero subspace. -/
theorem paper_grassmann_zero (d : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ E : Submodule ℝ (Euclid d), Module.finrank ℝ E = 0 →
      E ∈ ({⊥} : Finset (Submodule ℝ (Euclid d))) ∧
      ‖E.starProjection-(⊥ : Submodule ℝ (Euclid d)).starProjection‖ < ζ := by
  intro E hE
  have hz : E=⊥ := Submodule.finrank_eq_zero.mp hE
  subst E
  simp [hζ]
end GaussianEllipsoid.UCFrameGeometry
#print axioms GaussianEllipsoid.UCFrameGeometry.paper_grassmann_projection_net
#print axioms GaussianEllipsoid.UCFrameGeometry.paper_grassmann_zero
