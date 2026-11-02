import PolarDuality

noncomputable section
open scoped BigOperators
namespace GaussianEllipsoid

/-- Sharp dimension-dependent comparison between nuclear and Frobenius norms. -/
theorem spectralNuclear_le_sqrt_dim_mul_frobenius {r q : ℕ} (A : FrobeniusMatrix r q) :
    spectralNuclearNorm A ≤ Real.sqrt q * ‖A‖ := by
  have hsq : ∑ i, (singularValue (frobeniusOperator A) i) ^ 2 = ‖A‖ ^ 2 := by
    simp only [singularValue_eq_norm]
    rw [sum_norm_sq_operator_basis, operatorFrobenius_frobeniusOperator]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun _ : Fin q => (1 : ℝ)) (singularValue (frobeniusOperator A))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, hsq] at hcs
  apply (sq_le_sq₀ (spectralNuclear_nonneg A) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)]
  exact hcs

theorem spectralNuclear_sub_le {r q : ℕ} (A B : FrobeniusMatrix r q) :
    spectralNuclearNorm (A - B) ≤ spectralNuclearNorm A + spectralNuclearNorm B := by
  simpa only [sub_eq_add_neg, spectralNuclear_neg] using spectralNuclear_add_le A (-B)

theorem abs_sub_spectralNuclear_le {r q : ℕ} (A B : FrobeniusMatrix r q) :
    |spectralNuclearNorm A - spectralNuclearNorm B| ≤ spectralNuclearNorm (A - B) := by
  have h1 := spectralNuclear_add_le (A - B) B
  have h2 := spectralNuclear_add_le (B - A) A
  simp only [sub_add_cancel] at h1 h2
  have hn : spectralNuclearNorm (B - A) = spectralNuclearNorm (A - B) := by
    rw [← neg_sub A B, spectralNuclear_neg]
  rw [hn] at h2
  apply abs_le.mpr
  constructor <;> linarith

end GaussianEllipsoid
#print axioms GaussianEllipsoid.spectralNuclear_le_sqrt_dim_mul_frobenius
#print axioms GaussianEllipsoid.spectralNuclear_sub_le
#print axioms GaussianEllipsoid.abs_sub_spectralNuclear_le
