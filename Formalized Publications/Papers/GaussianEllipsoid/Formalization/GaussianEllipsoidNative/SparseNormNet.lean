import GaussianFixedVector

noncomputable section
open MeasureTheory GaussianTensorMoments
open scoped InnerProductSpace BigOperators
namespace GaussianEllipsoid.SparseSupport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A quarter-net controls the upper operator norm with loss 4/3. -/
theorem opNorm_le_of_quarter_net (T : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x-y‖ ≤ 1/4)
    {M : ℝ} (hM : 0 ≤ M) (hs : ∀ y ∈ s, ‖T y‖ ≤ M) : ‖T‖ ≤ 4*M/3 := by
  have hbound : ‖T‖ ≤ M + ‖T‖/4 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    calc ‖T x‖ = ‖T y + T (x-y)‖ := by congr 1; rw [map_sub]; abel
      _ ≤ ‖T y‖ + ‖T (x-y)‖ := norm_add_le _ _
      _ ≤ M + ‖T‖ * ‖x-y‖ := add_le_add (hs y hy) (T.le_opNorm _)
      _ ≤ M + ‖T‖/4 := by nlinarith [norm_nonneg T]
  linarith

/-- A direct norm-net proof of a conservative quadratic lower bound. It avoids
an extremizing eigenvector or a smallest-singular-value infimum. -/
theorem norm_sq_lower_of_quarter_net (T : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x-y‖ ≤ 1/4)
    {H : ℝ} (hH : 0 ≤ H)
    (hs : ∀ y ∈ s, |‖T y‖^2-H| ≤ H/4) :
    ∀ x : E, H/5 * ‖x‖^2 ≤ ‖T x‖^2 := by
  let a := Real.sqrt H
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha₂ : a^2 = H := Real.sq_sqrt hH
  have hupper : ‖T‖ ≤ 3*a/2 := by
    have hup (y : E) (hy : y ∈ s) : ‖T y‖ ≤ 9*a/8 := by
      have hb := (abs_le.mp (hs y hy)).2
      nlinarith [norm_nonneg (T y)]
    have ht := opNorm_le_of_quarter_net T s hnet (show 0 ≤ 9*a/8 by positivity) hup
    linarith
  have hunit (x : E) (hx : ‖x‖ = 1) : H/5 ≤ ‖T x‖^2 := by
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    have hlow : 5*a/6 ≤ ‖T y‖ := by
      have hb := (abs_le.mp (hs y hy)).1
      nlinarith [norm_nonneg (T y)]
    have hdiff : ‖T (x-y)‖ ≤ 3*a/8 := by
      calc ‖T (x-y)‖ ≤ ‖T‖*‖x-y‖ := T.le_opNorm _
        _ ≤ (3*a/2)*(1/4) := mul_le_mul hupper hxy (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have htriangle : ‖T y‖ ≤ ‖T x‖ + ‖T (x-y)‖ := by
      calc ‖T y‖ = ‖T x - T (x-y)‖ := by congr 1; rw [map_sub]; abel
        _ ≤ _ := norm_sub_le _ _
    have hlx : 11*a/24 ≤ ‖T x‖ := by linarith
    nlinarith [norm_nonneg (T x)]
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnx : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hb := hunit (‖x‖⁻¹ • x) hnx
  rw [map_smul, norm_smul, norm_inv, norm_norm, mul_pow] at hb
  have hmul := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)
  have heq : (‖x‖⁻¹)^2 * ‖T x‖^2 * ‖x‖^2 = ‖T x‖^2 := by
    field_simp
  rwa [heq] at hmul

/-- One genuine Gaussian matrix has a simultaneous all-vector lower bound
except on at most 2·9^n·exp(-h/256) of its actual probability space. -/
theorem gaussianMatrixCLM_lower_tail (h n : ℕ) :
    (gaussianProductLaw (Fin h × Fin n)).real
      {x | ∃ v : EuclideanSpace ℝ (Fin n),
        ‖gaussianMatrixCLM h n x v‖^2 < (h : ℝ)/5 * ‖v‖^2} ≤
          2 * (9 : ℝ)^n * Real.exp (-(h : ℝ)/256) := by
  classical
  obtain ⟨s, hsn, hsc, hsnet⟩ := GaussianEllipsoid.exists_sphere_quarter_net n
  let ev (v : EuclideanSpace ℝ (Fin n)) :=
    {x : (Fin h × Fin n) → ℝ | (h : ℝ)/4 ≤ |‖gaussianMatrixCLM h n x v‖^2-h|}
  have hsub : {x | ∃ v : EuclideanSpace ℝ (Fin n),
        ‖gaussianMatrixCLM h n x v‖^2 < (h : ℝ)/5 * ‖v‖^2} ⊆ ⋃ v ∈ s, ev v := by
    intro x hx
    by_contra hh
    have hgood (v) (hv : v ∈ s) : |‖gaussianMatrixCLM h n x v‖^2-h| ≤ (h : ℝ)/4 := by
      apply le_of_lt
      apply lt_of_not_ge
      intro hbad
      exact hh (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, hbad⟩⟩)
    have hlower := norm_sq_lower_of_quarter_net (gaussianMatrixCLM h n x) s
      (fun v hv => by obtain ⟨w, hw, hd⟩ := hsnet v hv; exact ⟨w, hw, hd.le⟩)
      (Nat.cast_nonneg h) hgood
    obtain ⟨v, hv⟩ := hx
    exact not_lt_of_ge (hlower v) hv
  calc
    _ ≤ (gaussianProductLaw (Fin h × Fin n)).real (⋃ v ∈ s, ev v) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ v ∈ s, (gaussianProductLaw (Fin h × Fin n)).real (ev v) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ v ∈ s, 2 * Real.exp (-(h : ℝ)/256) :=
      Finset.sum_le_sum (fun v hv => gaussianMatrixCLM_fixed_vector_tail h n v (hsn v hv))
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : (s.card : ℝ) ≤ (9 : ℝ)^n := by exact_mod_cast hsc
      nlinarith [Real.exp_pos (-(h : ℝ)/256)]

end GaussianEllipsoid.SparseSupport
