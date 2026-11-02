import PaperHeadNuisanceStructure
import GaussianEllipsoid.QuotientDischarge

noncomputable section
open MeasureTheory Set Module
open scoped BigOperators
namespace UCEscape
open GaussianEllipsoid

/-- The ordered monomial span is exactly the paper's constant column plus the
range of centered quadratic measurements on symmetric head matrices. -/
theorem headNuisanceSpace_mem_iff_symmetric_quadratic {j n : ℕ} (h : Sample j n)
    (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ headNuisanceSpace h ↔ ∃ A : Square j, A.transpose=A ∧ ∃ b : ℝ,
      v=WithLp.toLp 2 (fun i => measurementQ h A i+b) := by
  classical
  constructor
  · intro hv
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
    let H : Square j := fun i k => a (some (i,k))
    let S : Square j := (1/2:ℝ) • (H+H.transpose)
    have hS : S.transpose=S := by
      simp only [S,Matrix.transpose_smul,Matrix.transpose_add,Matrix.transpose_transpose]
      rw [add_comm H.transpose H]
    have hq (x : Vector j) : quadratic S x=quadratic H x := by
      dsimp [S]
      rw [quadratic_smul,quadratic_add,quadratic_transpose]
      ring
    have hvq : v=WithLp.toLp 2 (fun i => quadratic H (h i)+a none) := by
      rw [← ha]
      ext i
      simp [headFeature,quadratic,Matrix.mulVec,dotProduct,H,
        Fintype.sum_prod_type,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm,add_comm]
    refine ⟨Real.sqrt 2 • S,?_,a none+Matrix.trace S,?_⟩
    · rw [Matrix.transpose_smul,hS]
    · rw [hvq]
      ext i
      simp only [PiLp.toLp_apply,measurementQ,quadratic_smul,Matrix.trace_smul,
        smul_eq_mul,hq]
      have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp
      ring
  · rintro ⟨A,hA,b,rfl⟩
    exact head_measurementQ_mem_nuisance h A b

#print axioms headNuisanceSpace_mem_iff_symmetric_quadratic
end UCEscape
