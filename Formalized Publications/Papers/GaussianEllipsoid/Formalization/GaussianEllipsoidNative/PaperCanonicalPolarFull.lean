import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.MeasurableSpace
import MeasurableHalfPolar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import PolarDuality
import OperatorFrobeniusEquiv
import SupportedPolar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute


set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter
open scoped Matrix Topology Matrix.Norms.L2Operator MatrixOrder
namespace GaussianEllipsoid.PaperCanonicalPolar

abbrev Mat (r q : ℕ) := Matrix (Fin r) (Fin q) ℝ

def euclideanEquiv (q : ℕ) : Mat q q ≃⋆ₐ[ℝ] (Euclid q →L[ℝ] Euclid q) :=
  Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℝ)

def inverseRoot {q : ℕ} (S : Mat q q) : Mat q q := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) S

def regularScalar (k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (max x 0)/(max x 0+((k:ℝ)+1)⁻¹)

lemma regularScalar_continuous (k : ℕ) : Continuous (regularScalar k) := by
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right _ _) (by positivity))

lemma regularScalar_tendsto (x : ℝ) :
    Tendsto (fun k => regularScalar k x) atTop (𝓝 ((Real.sqrt x)⁻¹)) := by
  by_cases hxnonpos : x≤0
  · simpa only [regularScalar,max_eq_right hxnonpos,Real.sqrt_zero,Real.sqrt_eq_zero_of_nonpos hxnonpos,zero_div,inv_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  have hxpos : 0<x := lt_of_not_ge hxnonpos
  have hx : 0≤x := hxpos.le
  have hzero : x≠0 := hxpos.ne'
  have hspos : 0<Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hlim : Tendsto (fun k : ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := (tendsto_const_nhds (x := Real.sqrt x)).div
    ((tendsto_const_nhds (x := x)).add hlim) (by simpa using hzero)
  have he : Real.sqrt x/x=(Real.sqrt x)⁻¹ := by
    field_simp [hzero,hspos.ne']
    nlinarith [Real.sq_sqrt hx]
  simpa only [regularScalar,max_eq_left hx,add_zero,he,Pi.div_apply] using! h

lemma finite_uniform_of_pointwise {α : Type*} {s : Set α} (hs : s.Finite)
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (h : ∀ x∈s,Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop s := by
  intro u hu
  apply hs.eventually_all.mpr
  intro x hx
  have hsingle : TendstoUniformlyOn f g atTop {x} :=
    tendstoUniformlyOn_singleton_iff_tendsto.mpr (h x hx)
  simpa only [Set.mem_singleton_iff,forall_eq] using hsingle u hu

lemma regular_cfc_tendsto {q : ℕ} (S : Mat q q) :
    Tendsto (fun k => cfc (regularScalar k) S) atTop (𝓝 (inverseRoot S)) := by
  by_cases hS : IsSelfAdjoint S
  · have hHerm : S.IsHermitian := hS
    have hfinite : (spectrum ℝ S).Finite := by
      rw [hHerm.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    apply tendsto_cfc_fun
    · exact finite_uniform_of_pointwise hfinite _ _ (fun x hx => regularScalar_tendsto x)
    · exact Eventually.of_forall (fun k => (regularScalar_continuous k).continuousOn)
  · simp only [cfc_apply_of_not_predicate S hS,inverseRoot]
    exact tendsto_const_nhds

lemma regular_cfc_measurable (q k : ℕ) :
    Measurable (fun S : Mat q q => cfc (regularScalar k) S) := by
  have hclosed : IsClosed {S : Mat q q | IsSelfAdjoint S} := by
    change IsClosed {S : Mat q q | star S=S}
    exact isClosed_eq continuous_star continuous_id
  have hc : ContinuousOn (fun S : Mat q q => cfc (regularScalar k) S)
      {S | IsSelfAdjoint S} := by
    exact ContinuousOn.cfc_of_mem_nhdsSet (s := Set.univ) (regularScalar k) Filter.univ_mem
      continuousOn_id (fun S hS => hS) (regularScalar_continuous k).continuousOn
  classical
  convert hc.measurable_piecewise (continuousOn_const (c := (0:Mat q q))) hclosed.measurableSet using 1
  funext S
  by_cases hS : IsSelfAdjoint S
  · simp [hS]
  · simp [hS,cfc_apply_of_not_predicate S hS]

/-- The Moore-Penrose inverse square root is Borel, including rank drops.
The proof uses continuous scalar regularizers and finite-spectrum convergence. -/
theorem inverseRoot_measurable (q : ℕ) : Measurable (inverseRoot (q := q)) := by
  apply measurable_of_tendsto_metrizable (regular_cfc_measurable q)
  exact tendsto_pi_nhds.mpr (fun S => regular_cfc_tendsto S)

theorem inverseRoot_gram_measurable (r q : ℕ) :
    Measurable (fun M : Mat r q => inverseRoot (Mᴴ*M)) := by
  apply (inverseRoot_measurable q).comp
  apply Matrix.measurable_iff.mpr
  intro i j
  have h : Measurable (fun M : Mat r q => ∑ k,M k i*M k j) := by
    apply Finset.measurable_sum
    intro k _
    exact (Matrix.measurable_apply (i := k) (j := i)).mul (Matrix.measurable_apply (i := k) (j := j))
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial] using! h

def canonicalPolar {r q : ℕ} (M : Mat r q) : Mat r q := M*inverseRoot (Mᴴ*M)

theorem canonicalPolar_measurable (r q : ℕ) : Measurable (canonicalPolar (r := r) (q := q)) := by
  have hroot := inverseRoot_gram_measurable r q
  apply Matrix.measurable_iff.mpr
  intro i j
  simp only [canonicalPolar,Matrix.mul_apply]
  apply Finset.measurable_sum
  intro k _
  exact (Matrix.measurable_apply (i := i) (j := k)).mul (hroot.eval_matrix (i := k) (j := j))

#print axioms inverseRoot_gram_measurable
#print axioms canonicalPolar_measurable
end GaussianEllipsoid.PaperCanonicalPolar


noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder InnerProductSpace
namespace GaussianEllipsoid.PaperCanonicalPolar

lemma cfc_mulVec_eigenvector {q : ℕ} (S : Mat q q) (hS : S.IsHermitian)
    (f : ℝ → ℝ) (v : Fin q → ℝ) (ev : ℝ) (hv : S*ᵥv=ev • v) :
    (cfc f S)*ᵥv=f ev • v := by
  let V : Mat q q := hS.eigenvectorUnitary
  let w := star V *ᵥ v
  have hVV : V*star V=1 := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hVV' : star V*V=1 := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hback : V*ᵥw=v := by rw [Matrix.mulVec_mulVec,hVV,Matrix.one_mulVec]
  have hdec : S=V*Matrix.diagonal hS.eigenvalues*star V := by
    simpa only [Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq,V] using hS.spectral_theorem
  have hdiag : Matrix.diagonal hS.eigenvalues*ᵥw=ev • w := by
    have h := congrArg (fun y => star V*ᵥy) hv
    rw [hdec,Matrix.mulVec_mulVec,← mul_assoc,← mul_assoc,hVV',one_mul,
      ← Matrix.mulVec_mulVec,Matrix.mulVec_smul] at h
    exact h
  have hcoeff (i : Fin q) : hS.eigenvalues i*w i=ev*w i := by
    have h := congrFun hdiag i
    simpa only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul] using h
  have hdiagF : Matrix.diagonal (fun i => f (hS.eigenvalues i))*ᵥw=f ev • w := by
    ext i
    simp only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul]
    by_cases hi : w i=0
    · simp [hi]
    · rw [(mul_right_cancel₀ hi (hcoeff i))]
  have hfdec : cfc f S=V*Matrix.diagonal (fun i => f (hS.eigenvalues i))*star V := by
    rw [hS.cfc_eq]
    simp only [Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq,V]
  rw [hfdec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  change V*ᵥ(Matrix.diagonal (fun i => f (hS.eigenvalues i))*ᵥw)=_
  rw [hdiagF,Matrix.mulVec_smul,hback]

lemma cfcCLM_eigenvector {q : ℕ} (S : Mat q q) (hS : S.IsHermitian)
    (f : ℝ → ℝ) (v : Euclid q) (ev : ℝ)
    (hv : (euclideanEquiv q) S v=ev • v) :
    (euclideanEquiv q) (cfc f S) v=f ev • v := by
  apply PiLp.ext
  intro i
  have hvec : S*ᵥv.ofLp=ev • v.ofLp := by
    exact congrArg WithLp.ofLp hv
  exact congrFun (cfc_mulVec_eigenvector S hS f v.ofLp ev hvec) i

/-- Canonical operator partial polar, with the zero-eigenvalue convention fixed
by the Moore-Penrose inverse-square-root scalar. -/
def canonicalOperator {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) : Euclid q →L[ℝ] Euclid r :=
  T ∘L (euclideanEquiv q) (inverseRoot
    ((euclideanEquiv q).symm (T.adjoint ∘L T)))

lemma canonicalOperator_basis {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) :
    canonicalOperator T (rightSingularBasis T i)=polarImage T i := by
  let S : Mat q q := (euclideanEquiv q).symm (T.adjoint ∘L T)
  have hself : IsSelfAdjoint (T.adjoint ∘L T) := by
    change ContinuousLinearMap.adjoint (T.adjoint ∘L T)=T.adjoint ∘L T
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hS : S.IsHermitian := hself.map (euclideanEquiv q).symm
  have heig := (gramSymmetric T).apply_eigenvectorBasis finrank_euclideanSpace_fin i
  have hv : (euclideanEquiv q) S (rightSingularBasis T i)=
      gramEigenvalue T i • rightSingularBasis T i := by
    simpa only [S,StarAlgEquiv.apply_symm_apply,rightSingularBasis,gramEigenvalue] using! heig
  have h := cfcCLM_eigenvector S hS (fun x => (Real.sqrt x)⁻¹)
    (rightSingularBasis T i) (gramEigenvalue T i) hv
  change T ((euclideanEquiv q) (inverseRoot S) (rightSingularBasis T i))=polarImage T i
  dsimp only [inverseRoot]
  rw [h,map_smul]
  rfl

/-- Identification with the existing exact SVD polar; this is equality of maps,
not just existence of some dual witness. -/
theorem canonicalOperator_eq_polarWitness {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    canonicalOperator T=polarWitness T := by
  apply ContinuousLinearMap.coe_injective
  apply (rightSingularBasis T).toBasis.ext
  intro i
  change canonicalOperator T (rightSingularBasis T i)=polarWitness T (rightSingularBasis T i)
  rw [polarWitness_basis]
  exact canonicalOperator_basis T i

#print axioms canonicalOperator_eq_polarWitness
end GaussianEllipsoid.PaperCanonicalPolar


noncomputable section
open MeasureTheory Module
open scoped InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GaussianEllipsoid.PaperCanonicalPolar

@[simp] theorem polarWitness_zero (r q : ℕ) :
    polarWitness (0 : Euclid q →L[ℝ] Euclid r)=0 := by
  rw [← canonicalOperator_eq_polarWitness]
  unfold canonicalOperator
  exact ContinuousLinearMap.zero_comp _

theorem canonical_polar_pairing {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    ⟪operatorFrobenius (polarWitness T),operatorFrobenius T⟫_ℝ=
      spectralNuclearNorm (operatorFrobenius T) := by
  rw [real_inner_comm]
  simpa only [frobeniusOperator_operatorFrobenius] using inner_polarWitness_eq_nuclear (operatorFrobenius T)

/-- The exact canonical SVD polar is Borel as an operator-valued function. -/
theorem polarWitness_measurable (r q : ℕ) :
    Measurable (polarWitness (r := r) (q := q)) := by
  have he : Continuous (euclideanEquiv q) :=
    (euclideanEquiv q).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have he' : Continuous (euclideanEquiv q).symm :=
    (euclideanEquiv q).symm.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hg : Continuous (fun T : Euclid q →L[ℝ] Euclid r =>
      (euclideanEquiv q).symm (T.adjoint ∘L T)) := by
    apply he'.comp
    fun_prop
  have hr := he.measurable.comp ((inverseRoot_measurable q).comp hg.measurable)
  have hm : Measurable (canonicalOperator (r := r) (q := q)) := by
    have hc : Measurable (fun p : (Euclid q →L[ℝ] Euclid r) × (Euclid q →L[ℝ] Euclid q) =>
        p.1 ∘L p.2) := (continuous_fst.clm_comp continuous_snd).measurable
    exact hc.comp (measurable_id.prodMk hr)
  have heq : canonicalOperator (r := r) (q := q)=polarWitness := funext canonicalOperator_eq_polarWitness
  rwa [heq] at hm

/-- Borel canonical partial polar in the project's source Frobenius coordinates. -/
theorem canonicalFrobeniusPolar_measurable (r q : ℕ) :
    Measurable (fun A : FrobeniusMatrix r q => operatorFrobenius (polarWitness (frobeniusOperator A))) :=
  (continuous_operatorFrobenius r q).measurable.comp
    ((polarWitness_measurable r q).comp (continuous_frobeniusOperator r q).measurable)

theorem canonicalFrobeniusPolar_formula {r q : ℕ} (A : FrobeniusMatrix r q) :
    operatorFrobenius (polarWitness (frobeniusOperator A)) =
      operatorFrobenius (canonicalOperator (frobeniusOperator A)) := by
  rw [canonicalOperator_eq_polarWitness]

lemma polarWitness_right_support {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (E : Euclid q →L[ℝ] Euclid q) (hE : E.adjoint=E) (hTE : T ∘L E=T) :
    polarWitness T ∘L E=polarWitness T := by
  let e := euclideanEquiv q
  let S : Mat q q := e.symm (T.adjoint ∘L T)
  have hET : E ∘L T.adjoint=T.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hTE
    simpa only [ContinuousLinearMap.adjoint_comp,hE] using h
  have hcomm : Commute (T.adjoint ∘L T) E := by
    change (T.adjoint ∘L T) ∘L E=E ∘L (T.adjoint ∘L T)
    rw [ContinuousLinearMap.comp_assoc,hTE,← ContinuousLinearMap.comp_assoc,hET]
  have hmat : Commute S (e.symm E) := hcomm.map e.symm
  have hroot := hmat.cfc_real (fun x : ℝ => (Real.sqrt x)⁻¹)
  have hR : e (inverseRoot S) ∘L E=E ∘L e (inverseRoot S) := by
    have h := congrArg e hroot.eq
    simpa only [map_mul,StarAlgEquiv.apply_symm_apply,inverseRoot] using! h
  simp only [← canonicalOperator_eq_polarWitness]
  change (T ∘L e (inverseRoot S)) ∘L E=T ∘L e (inverseRoot S)
  rw [ContinuousLinearMap.comp_assoc,hR,← ContinuousLinearMap.comp_assoc,hTE]

lemma polarWitness_left_support {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (D : Euclid r →L[ℝ] Euclid r) (hDT : D ∘L T=T) :
    D ∘L polarWitness T=polarWitness T := by
  simp only [← canonicalOperator_eq_polarWitness]
  unfold canonicalOperator
  rw [← ContinuousLinearMap.comp_assoc,hDT]

/-- The canonical partial polar itself is supported, attains the nuclear norm,
and has the exact rank-controlled energy required in the source. -/
theorem canonical_supported_polar {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (D : Euclid r →L[ℝ] Euclid r) (E : Euclid q →L[ℝ] Euclid q)
    (hDself : D.adjoint=D) (hEself : E.adjoint=E)
    (hDsq : D ∘L D=D) (hEsq : E ∘L E=E) (hT : D ∘L T ∘L E=T) :
    ‖polarWitness T‖≤1 ∧ D ∘L polarWitness T ∘L E=polarWitness T ∧
      ⟪operatorFrobenius T,operatorFrobenius (polarWitness T)⟫_ℝ=
        spectralNuclearNorm (operatorFrobenius T) ∧
      ‖operatorFrobenius (polarWitness T)‖^2≤(finrank ℝ (LinearMap.range E.toLinearMap):ℝ) := by
  have hTE : T ∘L E=T := by
    nth_rw 1 [← hT]
    rw [ContinuousLinearMap.comp_assoc,ContinuousLinearMap.comp_assoc,hEsq,hT]
  have hDT : D ∘L T=T := by
    nth_rw 1 [← hT]
    rw [← ContinuousLinearMap.comp_assoc,hDsq,hT]
  have hright := polarWitness_right_support T E hEself hTE
  have hleft := polarWitness_left_support T D hDT
  refine ⟨norm_polarWitness_le T,?_,?_,
    frobenius_supported_contraction_sq_le_rank _ E (norm_polarWitness_le T) hEself hEsq hright⟩
  · rw [← ContinuousLinearMap.comp_assoc,hleft,hright]
  · simpa only [frobeniusOperator_operatorFrobenius] using inner_polarWitness_eq_nuclear (operatorFrobenius T)

#print axioms polarWitness_measurable
#print axioms canonical_supported_polar
end GaussianEllipsoid.PaperCanonicalPolar
