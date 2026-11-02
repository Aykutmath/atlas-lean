import BMActualGOEMean

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments
open GaussianEllipsoid BMGeometry
open scoped BigOperators InnerProductSpace Matrix
namespace BMSpectralBridge

/-- The matrix trace observable is the actual Frobenius pairing for PSD S. -/
theorem trace_mul_eq_frobenius_inner {d : ℕ} (H S : Op d) (hS : IsPSD S) :
    Matrix.trace (opMatrix H * opMatrix S) =
      ⟪operatorFrobenius S, operatorFrobenius H⟫_ℝ := by
  have hsym := ((opMatrix_posSemidef_iff S).mpr hS).1
  have hij (i j : Fin d) : opMatrix S j i = opMatrix S i j := by
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hsym
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hh
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hij, PiLp.inner_apply,
    RCLike.inner_apply, star_trivial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem meanOp_pairing {n d : ℕ} (hn : 0 < n) (G : Fin n → Op d) (S : Op d)
    (hS : IsPSD S) (hfeasible : ∀ i, Matrix.trace (opMatrix (G i) * opMatrix S) = 1) :
    ⟪operatorFrobenius S, operatorFrobenius (meanOp n G)⟫_ℝ = Real.sqrt n := by
  have he : operatorFrobenius (meanOp n G) =
      (Real.sqrt n)⁻¹ • ∑ i, operatorFrobenius (G i) := by
    change operatorFrobeniusLinearEquiv d d ((Real.sqrt n)⁻¹ • ∑ i, G i) = _
    rw [map_smul, map_sum]
    rfl
  rw [he, real_inner_smul_right, inner_sum]
  simp_rw [← trace_mul_eq_frobenius_inner _ _ hS, hfeasible]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hn' : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  apply (mul_left_cancel₀ hn')
  rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul]
  nlinarith

/-- BM's deterministic final conversion. All premises concern the actual cone, Frobenius
radius, exact trace constraints and genuine operator norm; no spectral conclusions are inputs. -/
theorem feasible_fixed_spectralBox {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {κ R a C : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R) (ha : 0 < a) (hC : 0 < C)
    (haspect : a*(d:ℝ)^2 ≤ n) (G : Fin n → Op d) (S : Op d)
    (hS : S ∈ conditionCone d κ)
    (hradius : ‖operatorFrobenius S‖ ≤ R*Real.sqrt d)
    (hfeasible : ∀ i, Matrix.trace (opMatrix (G i) * opMatrix S) = 1)
    (hmean : ‖meanOp n G‖ ≤ C) :
    opMatrix S ∈ BMRescaling.spectralBox d (Real.sqrt a/(C*κ)) (κ*R) := by
  have hpair := meanOp_pairing hn G S hS.1 hfeasible
  have hasqrt : Real.sqrt a * d ≤ Real.sqrt n := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact haspect
  have htrace : (Real.sqrt a/C)*d ≤ opTrace S :=
    trace_lower_of_dual_pairing hS.1 hC hmean (by
      rw [hpair, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hasqrt)
  have henergy : ‖operatorFrobenius S‖^2 ≤ R^2*d := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hradius
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hh
  have hbox := conditioned_trace_energy_spectralBox hd hS hκ (sq_nonneg R) henergy htrace
  simpa only [div_div, Real.sqrt_sq hR] using hbox

/-- Concrete cutoff 32, with dimension-free fixed endpoints. -/
theorem feasible_fixed_spectralBox_thirtytwo {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {κ R a : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R) (ha : 0 < a)
    (haspect : a*(d:ℝ)^2 ≤ n) (G : Fin n → Op d) (S : Op d)
    (hS : S ∈ conditionCone d κ) (hradius : ‖operatorFrobenius S‖ ≤ R*Real.sqrt d)
    (hfeasible : ∀ i, Matrix.trace (opMatrix (G i) * opMatrix S) = 1)
    (hmean : ‖meanOp n G‖ ≤ 32) :
    opMatrix S ∈ BMRescaling.spectralBox d (Real.sqrt a/(32*κ)) (κ*R) :=
  feasible_fixed_spectralBox hn hd hκ hR ha (by norm_num) haspect G S hS hradius hfeasible hmean

end BMSpectralBridge

namespace BMSpectralBridge

/-- Exact trace identity used in BM §3.1.4. -/
theorem meanOp_trace {n d : ℕ} (hn : 0 < n) (G : Fin n → Op d) (S : Op d)
    (hS : IsPSD S) (hfeasible : ∀ i, Matrix.trace (opMatrix (G i) * opMatrix S) = 1) :
    Matrix.trace (opMatrix (meanOp n G) * opMatrix S) = Real.sqrt n := by
  rw [trace_mul_eq_frobenius_inner _ _ hS]
  exact meanOp_pairing hn G S hS hfeasible

end BMSpectralBridge
