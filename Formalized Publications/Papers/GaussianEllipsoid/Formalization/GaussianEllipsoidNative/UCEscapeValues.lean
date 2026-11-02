import BMGordonExpectations
import UCEscapeStatistic
import UCEscapeOrderAux
import GordonCompactPassage
import UCMinimumExpectation
import UCPSDGaussianMinimum

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle BMGordon
namespace UCEscape

theorem primary_eq_blocks_general {n d : ℕ}
    (u : Euclid n) (S : HMat d) (ω : Space n d) :
    ⟪primaryCoefficient u S,ω⟫_ℝ = ⟪matrixBlock ω,tensor u S⟫_ℝ + scalarBlock ω := by
  change (∑ i : Index n d, ω i * primaryCoefficient u S i) = _
  simp only [Fintype.sum_sum_type,primaryCoefficient,
    Sum.elim_inl,Sum.elim_inr,mul_zero,Finset.sum_const_zero,add_zero]
  change (∑ i : EntryIndex n d, matrixBlock ω i * tensor u S i) +
    (∑ i : Unit, ω (.inl (.inr i))*1) +
    ((∑ i : Fin d × Fin d, ω (.inr (.inl i))*0)+(∑ i : Fin n, ω (.inr (.inr i))*0)) = _
  simp only [mul_one,mul_zero,Fintype.sum_unique,Finset.sum_const_zero,add_zero]
  change (∑ i : EntryIndex n d, matrixBlock ω i * tensor u S i) + scalarBlock ω = _
  congr 1
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.star_apply,star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem auxiliary_eq_blocks_general {n d : ℕ}
    (u : Euclid n) (S : HMat d) (ω : Space n d) :
    ⟪auxiliaryCoefficient u S,ω⟫_ℝ = ⟪widthMatrix ω,(S : HMat d)⟫_ℝ + ⟪(u : Euclid n),driftBlock ω⟫_ℝ := by
  change (∑ i : Index n d, ω i * auxiliaryCoefficient u S i) = _
  simp only [Fintype.sum_sum_type,auxiliaryCoefficient,
    Sum.elim_inl,Sum.elim_inr,mul_zero,Finset.sum_const_zero,zero_add]
  change ((∑ i : EntryIndex n d, ω (.inl (.inl i))*0)+(∑ i : Unit, ω (.inl (.inr i))*0))+
    ((∑ i : Fin d × Fin d, widthBlock ω i*frobeniusEquivEuclidean d d S i)+
    ∑ i : Fin n, driftBlock ω i*(u : Euclid n) i) = _
  simp only [mul_zero,Finset.sum_const_zero,zero_add]
  change ⟪frobeniusEquivEuclidean d d S,widthBlock ω⟫_ℝ +
    ⟪(u : Euclid n),driftBlock ω⟫_ℝ = _
  congr 1
  rw [← LinearIsometryEquiv.inner_map_map (frobeniusEquivEuclidean d d)]
  simp only [widthMatrix,LinearIsometryEquiv.apply_symm_apply]
  exact real_inner_comm _ _


variable {J : Type*} [Nonempty J] {n d r : ℕ}

abbrev EscapeIndex (J : Type*) (d : ℕ) := J × ↥(psdUnit d)

def escapePrimary (U : J → Euclid r →ₗᵢ[ℝ] Euclid n)
    (p : EscapeIndex J d × UnitSample r) (ω : Space n d) : ℝ :=
  ⟪primaryCoefficient (U p.1.1 p.2) p.1.2,ω⟫_ℝ

def escapeAuxiliary (U : J → Euclid r →ₗᵢ[ℝ] Euclid n)
    (p : EscapeIndex J d × UnitSample r) (ω : Space n d) : ℝ :=
  ⟪auxiliaryCoefficient (U p.1.1 p.2) p.1.2,ω⟫_ℝ

theorem escapePrimary_row_sup (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (p : EscapeIndex J d) (ω : Space n d) :
    sSup ((fun u : UnitSample r => escapePrimary U (p,u) ω) '' Set.univ) =
      ‖(U p.1).toContinuousLinearMap.adjoint (measurement (matrixBlock ω) p.2)‖ + scalarBlock ω := by
  have he (u : UnitSample r) : escapePrimary U (p,u) ω =
      ⟪(u : Euclid r),(U p.1).toContinuousLinearMap.adjoint (measurement (matrixBlock ω) p.2)⟫_ℝ + scalarBlock ω := by
    rw [escapePrimary, primary_eq_blocks_general, ← combine_pairing, ← measurement_pairing]
    congr 1
    exact ((U p.1).toContinuousLinearMap.adjoint_inner_right u _).symm
  simp_rw [he]
  exact inner_unitSphere_sup_add hr _ _

theorem escapePrimary_value (hd : 0 < d) (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (ω : Space n d) :
    BMGordonCompact.compactMinMax (escapePrimary (d := d) U) ω =
      projectedEscape U (matrixBlock ω) + scalarBlock ω := by
  letI : Nonempty ↥(psdUnit d) := (psdUnit_nonempty hd).to_subtype
  unfold BMGordonCompact.compactMinMax
  simp_rw [escapePrimary_row_sup hr]
  rw [Set.image_univ]
  exact csInf_range_add _ (projectedEscape_bddBelow U (matrixBlock ω)) _

theorem escapeAuxiliary_row_sup (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (p : EscapeIndex J d) (ω : Space n d) :
    sSup ((fun u : UnitSample r => escapeAuxiliary U (p,u) ω) '' Set.univ) =
      ‖(U p.1).toContinuousLinearMap.adjoint (driftBlock ω)‖ + ⟪widthMatrix ω,(p.2 : HMat d)⟫_ℝ := by
  have he (u : UnitSample r) : escapeAuxiliary U (p,u) ω =
      ⟪(u : Euclid r),(U p.1).toContinuousLinearMap.adjoint (driftBlock ω)⟫_ℝ +
        ⟪widthMatrix ω,(p.2 : HMat d)⟫_ℝ := by
    rw [escapeAuxiliary, auxiliary_eq_blocks_general]
    have h := (U p.1).toContinuousLinearMap.adjoint_inner_right (u : Euclid r) (driftBlock ω)
    change ⟪(u : Euclid r),(U p.1).toContinuousLinearMap.adjoint (driftBlock ω)⟫_ℝ =
      ⟪U p.1 u,driftBlock ω⟫_ℝ at h
    rw [h, add_comm]
  simp_rw [he]
  exact inner_unitSphere_sup_add hr _ _

theorem escapeAuxiliary_value [Fintype J] (hd : 0 < d) (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (ω : Space n d) :
    BMGordonCompact.compactMinMax (escapeAuxiliary (d := d) U) ω =
      projectedNormMinimum n r U (driftBlock ω) + psdMinimum d (widthMatrix ω) := by
  classical
  obtain ⟨S,hS,hmin⟩ := (psdUnit_compact d).exists_isMinOn (psdUnit_nonempty hd)
    (show ContinuousOn (fun S : HMat d => ⟪widthMatrix ω,S⟫_ℝ) (psdUnit d) from
      (continuous_const.inner continuous_id).continuousOn)
  have hsEq : psdMinimum d (widthMatrix ω) = ⟪widthMatrix ω,S⟫_ℝ := by
    apply IsLeast.csInf_eq
    refine ⟨⟨S,hS,rfl⟩, ?_⟩
    rintro y ⟨T,hT,rfl⟩
    exact hmin hT
  obtain ⟨j,hj,hjEq⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty : (Finset.univ : Finset J).Nonempty)
    (fun j => ‖(U j).toContinuousLinearMap.adjoint (driftBlock ω)‖)
  change projectedNormMinimum n r U (driftBlock ω) = _ at hjEq
  unfold BMGordonCompact.compactMinMax
  simp_rw [escapeAuxiliary_row_sup hr]
  apply IsLeast.csInf_eq
  refine ⟨⟨(j,⟨S,hS⟩),Set.mem_univ _, ?_⟩, ?_⟩
  · rw [hsEq,hjEq]
  · rintro y ⟨p,_,rfl⟩
    have h1 : projectedNormMinimum n r U (driftBlock ω) ≤
        ‖(U p.1).toContinuousLinearMap.adjoint (driftBlock ω)‖ :=
      Finset.inf'_le _ (Finset.mem_univ _)
    have h2 : psdMinimum d (widthMatrix ω) ≤ ⟪widthMatrix ω,(p.2 : HMat d)⟫_ℝ :=
      csInf_le (psd_values_bddBelow d (widthMatrix ω)) ⟨p.2,p.2.property,rfl⟩
    exact add_le_add h1 h2

#print axioms escapeAuxiliary_value

#print axioms escapePrimary_value
end UCEscape
