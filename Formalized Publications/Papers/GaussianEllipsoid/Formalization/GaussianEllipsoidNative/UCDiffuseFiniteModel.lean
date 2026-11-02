import UCDiffuseNets
import UCUniformContinuity

/-! Concrete finite candidate model for the diffuse PSD class and an arbitrary
fixed nuisance subspace, with exact source-matrix norm adapters. -/
noncomputable section
open Module
open scoped BigOperators
namespace GaussianEllipsoid.UCDiffuseFiniteModel
open UCContinuityGeometry UCUniformContinuity UCDiffuseNets

 def sourceDiffuseClass (d : ℕ) (τ : ℝ) : Set (Square d) :=
  {A | A.PosSemidef ∧ frobeniusNorm A = 1 ∧ matrixOpNorm A ≤ τ}

 theorem psd_transpose {d : ℕ} {A : Square d} (hA : A.PosSemidef) : A.transpose = A := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian

 theorem ofMatrix_mem_diffuse {d : ℕ} {τ : ℝ} {A : Square d}
    (hA : A ∈ sourceDiffuseClass d τ) :
    ofMatrix A (psd_transpose hA.1) ∈ diffuseClass d τ := by
  change (matrix (ofMatrix A _)).PosSemidef ∧ ‖ofMatrix A _‖ = 1 ∧
    matrixOpNorm (matrix (ofMatrix A _)) ≤ τ
  simpa only [matrix_ofMatrix, norm_ofMatrix] using (show A.PosSemidef ∧ frobeniusNorm A = 1 ∧ matrixOpNorm A ≤ τ from hA)

 theorem frobenius_matrix_sub {d : ℕ} (A B : SymFrob d) :
    frobeniusNorm (matrix A-matrix B) = ‖A-B‖ := by
  change frobeniusNorm (matrix (A-B)) = ‖A-B‖
  exact matrix_frobeniusNorm _

 theorem source_diffuse_nonempty_iff (d : ℕ) (τ : ℝ) :
    (sourceDiffuseClass d τ).Nonempty ↔ (diffuseClass d τ).Nonempty := by
  constructor
  · rintro ⟨A,hA⟩
    exact ⟨ofMatrix A (psd_transpose hA.1), ofMatrix_mem_diffuse hA⟩
  · rintro ⟨A,hA⟩
    exact ⟨matrix A, hA.1, by rw [matrix_frobeniusNorm]; exact hA.2.1, hA.2.2⟩

/-- Product of the two actual covers is a joint matrix/nuisance cover. -/
theorem joint_cover {d n : ℕ} {τ ρ σ B : ℝ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (s : Finset (SymFrob d)) (t : Finset L)
    (hcoverD : ∀ A ∈ diffuseClass d τ, ∃ S ∈ s, ‖A-S‖ < ρ)
    (hcoverL : ∀ v : L, ‖v‖ ≤ B*n → ∃ w ∈ t, ‖v-w‖ < σ) :
    ∀ A ∈ sourceDiffuseClass d τ, ∀ v : EuclideanSpace ℝ (Fin n), v ∈ L → ‖v‖ ≤ B*n →
      ∃ k : ↥s × ↥t, frobeniusNorm (A-matrix k.1.val) < ρ ∧ ‖v-k.2.val.val‖ < σ := by
  intro A hA v hv hB
  let A' := ofMatrix A (psd_transpose hA.1)
  obtain ⟨S,hSs,hAS⟩ := hcoverD A' (ofMatrix_mem_diffuse hA)
  obtain ⟨w,hwt,hvw⟩ := hcoverL (⟨v,hv⟩ : L) hB
  refine ⟨(⟨S,hSs⟩,⟨w,hwt⟩), ?_, hvw⟩
  have he : frobeniusNorm (A-matrix S) = ‖A'-S‖ := by
    rw [← frobenius_matrix_sub, matrix_ofMatrix]
  rwa [he]

/-- Internal matrix-net centers satisfy every exact source diffuse condition. -/
theorem candidate_matrix_conditions {d : ℕ} {τ : ℝ} (s : Finset (SymFrob d))
    (hs : ∀ A ∈ s, A ∈ diffuseClass d τ) (k : ↥s) :
    (matrix k.val).PosSemidef ∧ (matrix k.val).transpose = matrix k.val ∧
      frobeniusNorm (matrix k.val) = 1 ∧ matrixOpNorm (matrix k.val) ≤ τ := by
  have h := hs k.val k.property
  exact ⟨h.1, matrix_transpose _, by rw [matrix_frobeniusNorm]; exact h.2.1, h.2.2⟩

#print axioms joint_cover
#print axioms candidate_matrix_conditions
end GaussianEllipsoid.UCDiffuseFiniteModel
