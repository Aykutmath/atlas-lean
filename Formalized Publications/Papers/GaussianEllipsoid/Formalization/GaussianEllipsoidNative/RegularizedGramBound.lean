import RegularizedGramConvex

noncomputable section
open Matrix Finset

namespace GaussianEllipsoid.CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Determinant of a scalar ridge plus a positive-semidefinite matrix. -/
theorem det_scalar_add_posSemidef {H : Matrix ι ι ℝ} (hH : H.PosSemidef) (ε : ℝ) :
    (ε • (1 : Matrix ι ι ℝ) + H).det =
      ∏ i, (ε + hH.isHermitian.eigenvalues i) := by
  let U := hH.isHermitian.eigenvectorUnitary
  have hdecomp : ε • (1 : Matrix ι ι ℝ) + H =
      (U : Matrix ι ι ℝ) * Matrix.diagonal (fun i => ε + hH.isHermitian.eigenvalues i) *
        (star (U : Matrix ι ι ℝ)) := by
    have hd : Matrix.diagonal (fun i => ε + hH.isHermitian.eigenvalues i) =
        ε • (1 : Matrix ι ι ℝ) + Matrix.diagonal (RCLike.ofReal ∘ hH.isHermitian.eigenvalues) := by
      ext i j
      by_cases hij : i = j
      · subst j; simp
      · simp [Matrix.diagonal_apply, hij]
    rw [hd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one]
    have hU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := by
      exact (Matrix.mem_unitaryGroup_iff).mp U.2
    rw [hU]
    congr 1
    exact hH.isHermitian.spectral_theorem
  rw [hdecomp, Matrix.det_mul_right_comm]
  simp [U]

/-- The positive ridge gives a deterministic lower bound on the determinant. -/
theorem det_scalar_add_posSemidef_ge {H : Matrix ι ι ℝ} (hH : H.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ε ^ Fintype.card ι ≤ (ε • (1 : Matrix ι ι ℝ) + H).det := by
  rw [det_scalar_add_posSemidef hH ε]
  have hp := Finset.prod_le_prod (s := (Finset.univ : Finset ι))
    (f := fun _ => ε) (g := fun i => ε + hH.isHermitian.eigenvalues i)
    (fun _ _ => hε) (fun i _ => le_add_of_nonneg_right (hH.eigenvalues_nonneg i))
  simpa using hp

/-- Explicit bound preventing improper Bochner-integral shortcuts. -/
theorem regularized_det_neg_nat_zpow_le {ε : ℝ} (hε : 0 < ε)
    (g : κ → ι → ℝ) {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (s : ℕ) :
    (regularizedGram ε g w).det ^ (-(s : ℤ)) ≤
      (ε ^ Fintype.card ι) ^ (-(s : ℤ)) := by
  exact neg_nat_zpow_antitone s (pow_pos hε _)
    (det_scalar_add_posSemidef_ge (weightedGram_posSemidef g hw) (le_of_lt hε))

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.regularized_det_neg_nat_zpow_le
