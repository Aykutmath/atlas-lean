import SpectralFrobenius

/-! Dimension-sharp internal nets of orthonormal frames, in genuine Frobenius norm. -/
noncomputable section
open GaussianEllipsoid Module
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.UCFrameGeometry

abbrev IsFrame {d j : ℕ} (U : FrobeniusMatrix d j) : Prop :=
  Orthonormal ℝ (fun i => U i)

theorem frame_norm_sq {d j : ℕ} {U : FrobeniusMatrix d j} (hU : IsFrame U) :
    ‖U‖^2 = (j:ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [hU.norm_eq_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem frame_norm {d j : ℕ} {U : FrobeniusMatrix d j} (hU : IsFrame U) :
    ‖U‖ = Real.sqrt (j:ℝ) := by
  rw [← frame_norm_sq hU, Real.sqrt_sq (norm_nonneg _)]

theorem column_norm_le_frobenius {d j : ℕ} (A : FrobeniusMatrix d j) (i : Fin j) :
    ‖A i‖ ≤ ‖A‖ := by
  have h := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin j))) =>
    sq_nonneg ‖A k‖) (Finset.mem_univ i)
  rw [← PiLp.norm_sq_eq_of_L2] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Centers remain genuine orthonormal frames; the exponent is exactly d*j.
Empty frame spaces and j=0 are included with no separate assumptions. -/
theorem exists_internal_frame_net (d j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset (FrobeniusMatrix d j),
      (∀ U ∈ N, IsFrame U) ∧
      (N.card:ℝ) ≤ (1+2*Real.sqrt (j:ℝ)/ε)^(d*j) ∧
      ∀ U : FrobeniusMatrix d j, IsFrame U → ∃ V ∈ N, ‖U-V‖ < ε := by
  obtain ⟨N,hN,hcard,hcover,_⟩ := exists_internal_net
    {U : FrobeniusMatrix d j | IsFrame U}
    (R := Real.sqrt (j:ℝ)) (Real.sqrt_nonneg _) hε
    (fun U hU => (frame_norm hU).le)
  exact ⟨N,hN,by simpa only [finrank_frobenius] using hcard,
    fun U hU => by simpa only [dist_eq_norm] using hcover U hU⟩

end GaussianEllipsoid.UCFrameGeometry
