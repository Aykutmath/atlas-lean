import PaperSymmetricSteinAggregate
import PaperWickAdapter

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory GaussianTensorMoments
open GaussianEllipsoid GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperQGaussian
open PaperSymmetricPullback PaperIsonormal
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)

lemma q_orthonormal (d : ℕ) : Orthonormal ℝ (qSym d) :=
  orthonormal_iff_ite.mpr (fun a b => qSym_inner a b)

lemma q_span_top (d : ℕ) : ⊤≤Submodule.span ℝ (Set.range (qSym d)) := by
  intro M hM
  rw [← synth_coordinates M,synth_apply]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a,rfl⟩)

def qBasis (d : ℕ) : OrthonormalBasis (Index d) ℝ (SymFrob d) :=
  OrthonormalBasis.mk (q_orthonormal d) (q_span_top d)

@[simp] theorem qBasis_apply (d : ℕ) (a : Index d) : qBasis d a=qSym d a := by
  simp only [qBasis,OrthonormalBasis.coe_mk]

def qSum (d : ℕ) (g : Index d→ℝ) : SymFrob d := ∑ a,g a • qSym d a

theorem qSum_matrix (d : ℕ) (g : Index d→ℝ) :
    matrix (qSum d g)=∑ a,g a • PaperSymmetricDirections.Q a.val.1 a.val.2 := by
  rw [show qSum d g=synth d g by exact (synth_apply d g).symm]
  exact matrix_synth d g

/-- Literal independent Q-coordinate Gaussian sum, with no assumed Gaussian-law
premise and with the source Frobenius normalization. -/
theorem qSum_preserving (d : ℕ) :
    MeasurePreserving (qSum d) (gaussianProductLaw (Index d)) (stdGaussian (SymFrob d)) := by
  have he : qSum d=synth d := by funext g; exact (synth_apply d g).symm
  refine ⟨?_,?_⟩
  · rw [he]
    exact (synth d).continuous.measurable
  · change (Measure.pi (fun _ : Index d => gaussianReal 0 1)).map
        (fun g => ∑ a,g a • qSym d a)=stdGaussian (SymFrob d)
    simpa only [qBasis_apply] using
      (stdGaussian_eq_map_pi_orthonormalBasis (qBasis d)).symm

theorem qSum_isonormal (d : ℕ) :
    IsIsonormalSymLaw d ((gaussianProductLaw (Index d)).map (qSum d)) :=
  (isonormalSymLaw_iff_stdGaussian _ _).mpr (qSum_preserving d).map_eq

theorem qSum_mean_zero (d : ℕ) :
    (∫ g,qSum d g ∂gaussianProductLaw (Index d))=0 := by
  have h := integral_map (qSum_preserving d).aemeasurable
    (show AEStronglyMeasurable (fun x : SymFrob d => x)
      ((gaussianProductLaw (Index d)).map (qSum d)) from measurable_id.aestronglyMeasurable)
  rw [(qSum_preserving d).map_eq] at h
  exact h.symm.trans integral_id_stdGaussian

theorem qSum_covariance {d : ℕ} (A B : SymFrob d) :
    (∫ g,⟪qSum d g,A⟫_ℝ*⟪qSum d g,B⟫_ℝ ∂gaussianProductLaw (Index d))=⟪A,B⟫_ℝ := by
  have hc := covarianceBilin_apply (IsGaussian.memLp_id (stdGaussian (SymFrob d)) 2 (by simp)) A B
  simp only [id_eq] at hc
  rw [covarianceBilin_stdGaussian,integral_id_stdGaussian] at hc
  simp only [sub_zero,innerSL_apply_apply ℝ] at hc
  have hm : AEStronglyMeasurable (fun x : SymFrob d => ⟪x,A⟫_ℝ*⟪x,B⟫_ℝ)
      ((gaussianProductLaw (Index d)).map (qSum d)) := by
    exact (by fun_prop : Measurable (fun x : SymFrob d => ⟪x,A⟫_ℝ*⟪x,B⟫_ℝ)).aestronglyMeasurable
  have ht := integral_map (qSum_preserving d).aemeasurable hm
  rw [(qSum_preserving d).map_eq] at ht
  apply ht.symm.trans
  simpa only [real_inner_comm] using hc.symm

theorem qSum_covariance_trace {d : ℕ} (A B : SymFrob d) :
    (∫ g,⟪qSum d g,A⟫_ℝ*⟪qSum d g,B⟫_ℝ ∂gaussianProductLaw (Index d))=
      Matrix.trace (matrix A*matrix B) := by
  rw [qSum_covariance,symFrob_inner_matrix]
  exact PaperWickAdapter.frobenius_pairing_eq_trace _ _ (matrix_transpose B)

/-- Independent copies of the exact source sum have the full iid isonormal
row law. The row count is arbitrary, including the empty family. -/
theorem qRows_preserving (d n : ℕ) :
    MeasurePreserving (fun g : Fin n→Index d→ℝ => fun i => qSum d (g i))
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Index d)))
      (Measure.pi (fun _ : Fin n => stdGaussian (SymFrob d))) :=
  measurePreserving_pi _ _ (fun _ => qSum_preserving d)

#print axioms qSum_preserving
#print axioms qSum_isonormal
#print axioms qSum_mean_zero
#print axioms qSum_covariance_trace
#print axioms qRows_preserving
end GaussianEllipsoid.PaperQGaussian
