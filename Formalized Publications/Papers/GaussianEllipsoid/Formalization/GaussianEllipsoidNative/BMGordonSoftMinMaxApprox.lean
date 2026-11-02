import BMGordonSoftMinMax

noncomputable section
open scoped BigOperators

namespace BMGordonSoftMinMax
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- The maximum within a finite nonempty row. -/
def rowMax (x : I × J → ℝ) (i : I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => x (i,j))

/-- The exact minimum of the row maxima. -/
def minMax (x : I × J → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (rowMax x)

omit [Fintype I] [Nonempty I] in
theorem le_rowMax (x : I × J → ℝ) (i : I) (j : J) : x (i,j) ≤ rowMax x i :=
  Finset.le_sup' (fun j => x (i,j)) (Finset.mem_univ j)

omit [Fintype I] [Nonempty I] in
theorem rowMax_attained (x : I × J → ℝ) (i : I) : ∃ j, rowMax x i = x (i,j) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => x (i,j))
  exact ⟨j, hj⟩

theorem minMax_le_rowMax (x : I × J → ℝ) (i : I) : minMax x ≤ rowMax x i :=
  Finset.inf'_le (rowMax x) (Finset.mem_univ i)

theorem minMax_attained (x : I × J → ℝ) : ∃ i, minMax x = rowMax x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (rowMax x)
  exact ⟨i, hi⟩

theorem minMax_eq_entry (x : I × J → ℝ) : ∃ a, minMax x = x a := by
  obtain ⟨i, hi⟩ := minMax_attained x
  obtain ⟨j, hj⟩ := rowMax_attained x i
  exact ⟨(i,j), hi.trans hj⟩

omit [Fintype I] [Nonempty I] in
theorem exp_rowMax_le_rowSum (β : ℝ) (x : I × J → ℝ) (i : I) :
    Real.exp (β * rowMax x i) ≤ rowSum β x i := by
  obtain ⟨j, hj⟩ := rowMax_attained x i
  rw [hj]
  exact Finset.single_le_sum (fun k _ => (Real.exp_pos (β * x (i,k))).le)
    (Finset.mem_univ j)

omit [Fintype I] [Nonempty I] in
theorem rowSum_le_card_mul_exp_rowMax (β : ℝ) (hβ : 0 ≤ β)
    (x : I × J → ℝ) (i : I) :
    rowSum β x i ≤ (Fintype.card J : ℝ) * Real.exp (β * rowMax x i) := by
  calc
    rowSum β x i ≤ ∑ _j : J, Real.exp (β * rowMax x i) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_rowMax x i j) hβ)
    _ = _ := by simp

/-- The upper partition estimate yields the lower soft-minmax bound. -/
theorem outerSum_le_card_mul_exp_minMax (β : ℝ) (hβ : 0 ≤ β)
    (x : I × J → ℝ) :
    outerSum β x ≤ (Fintype.card I : ℝ) * Real.exp (-β * minMax x) := by
  calc
    outerSum β x ≤ ∑ _i : I, Real.exp (-β * minMax x) := by
      apply Finset.sum_le_sum
      intro i hi
      have hrow : Real.exp (β * minMax x) ≤ rowSum β x i :=
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (minMax_le_rowMax x i) hβ)).trans
          (exp_rowMax_le_rowSum β x i)
      have hinv := one_div_le_one_div_of_le (Real.exp_pos (β * minMax x)) hrow
      simpa only [one_div, ← Real.exp_neg, neg_mul] using hinv
    _ = _ := by simp

/-- A minimizing row supplies the lower partition estimate. -/
theorem exp_minMax_div_card_le_outerSum (β : ℝ) (hβ : 0 ≤ β)
    (x : I × J → ℝ) :
    Real.exp (-β * minMax x) / (Fintype.card J : ℝ) ≤ outerSum β x := by
  obtain ⟨i, hi⟩ := minMax_attained x
  have hrow := rowSum_le_card_mul_exp_rowMax β hβ x i
  rw [← hi] at hrow
  have hinv := one_div_le_one_div_of_le (rowSum_pos β x i) hrow
  have hterm : Real.exp (-β * minMax x) / (Fintype.card J : ℝ) ≤
      (rowSum β x i)⁻¹ := by
    simpa only [one_div, mul_inv_rev, div_eq_mul_inv, ← Real.exp_neg, neg_mul, one_mul] using hinv
  exact hterm.trans (Finset.single_le_sum
    (fun k _ => (inv_pos.mpr (rowSum_pos β x k)).le) (Finset.mem_univ i))

/-- Sharp deterministic approximation to finite minmax by the actual smooth function. -/
theorem minMax_sub_log_card_le_softMinMax_le (β : ℝ) (hβ : 0 < β)
    (x : I × J → ℝ) :
    minMax x - Real.log (Fintype.card I : ℝ) / β ≤ softMinMax β x ∧
      softMinMax β x ≤ minMax x + Real.log (Fintype.card J : ℝ) / β := by
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos (α := I)
  have hJ : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos (α := J)
  have hupper := Real.log_le_log (outerSum_pos β x)
    (outerSum_le_card_mul_exp_minMax β hβ.le x)
  rw [Real.log_mul (ne_of_gt hI) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hupper
  have hlower := Real.log_le_log (div_pos (Real.exp_pos (-β * minMax x)) hJ)
    (exp_minMax_div_card_le_outerSum β hβ.le x)
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hJ), Real.log_exp] at hlower
  constructor
  · change _ ≤ -Real.log (outerSum β x) / β
    apply (le_div_iff₀ hβ).2
    have he : (minMax x - Real.log (Fintype.card I : ℝ) / β) * β =
        minMax x * β - Real.log (Fintype.card I : ℝ) := by field_simp
    rw [he]
    linarith
  · change -Real.log (outerSum β x) / β ≤ _
    apply (div_le_iff₀ hβ).2
    have he : (minMax x + Real.log (Fintype.card J : ℝ) / β) * β =
        minMax x * β + Real.log (Fintype.card J : ℝ) := by field_simp
    rw [he]
    linarith

/-- A convenient nonnegative bound for the absolute approximation error. -/
theorem abs_softMinMax_sub_minMax_le (β : ℝ) (hβ : 0 < β)
    (x : I × J → ℝ) :
    |softMinMax β x - minMax x| ≤
      Real.log (Fintype.card I : ℝ) / β + Real.log (Fintype.card J : ℝ) / β := by
  obtain ⟨hl, hu⟩ := minMax_sub_log_card_le_softMinMax_le β hβ x
  have hI : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos (α := I)
  have hJ : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast Fintype.card_pos (α := J)
  have hlogI := div_nonneg (Real.log_nonneg hI) hβ.le
  have hlogJ := div_nonneg (Real.log_nonneg hJ) hβ.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_minMax_le_sum_abs (x : I × J → ℝ) : |minMax x| ≤ ∑ a, |x a| := by
  obtain ⟨a, ha⟩ := minMax_eq_entry x
  rw [ha]
  exact Finset.single_le_sum (fun b _ => abs_nonneg (x b)) (Finset.mem_univ a)

/-- Global growth control suitable for Gaussian integrability and dominated convergence. -/
theorem abs_softMinMax_le_sum_abs_add_logs (β : ℝ) (hβ : 0 < β)
    (x : I × J → ℝ) :
    |softMinMax β x| ≤ ∑ a, |x a| +
      Real.log (Fintype.card I : ℝ) / β + Real.log (Fintype.card J : ℝ) / β := by
  calc
    |softMinMax β x| = |softMinMax β x - minMax x + minMax x| := by congr 1; ring
    _ ≤ |softMinMax β x - minMax x| + |minMax x| := abs_add_le _ _
    _ ≤ (Real.log (Fintype.card I : ℝ) / β + Real.log (Fintype.card J : ℝ) / β) +
        ∑ a, |x a| := add_le_add (abs_softMinMax_sub_minMax_le β hβ x)
          (abs_minMax_le_sum_abs x)
    _ = _ := by ring

/-- For inverse temperatures at least one, the growth bound is uniform in β. -/
theorem abs_softMinMax_le_sum_abs_add_logs_uniform (β : ℝ) (hβ : 1 ≤ β)
    (x : I × J → ℝ) :
    |softMinMax β x| ≤ ∑ a, |x a| +
      Real.log (Fintype.card I : ℝ) + Real.log (Fintype.card J : ℝ) := by
  have hI : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos (α := I)
  have hJ : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast Fintype.card_pos (α := J)
  have hbound := abs_softMinMax_le_sum_abs_add_logs β (lt_of_lt_of_le zero_lt_one hβ) x
  have hlI := div_le_self (Real.log_nonneg hI) hβ
  have hlJ := div_le_self (Real.log_nonneg hJ) hβ
  linarith

/-- The genuine nested soft minmax converges pointwise to exact finite minmax. -/
theorem tendsto_softMinMax (x : I × J → ℝ) :
    Filter.Tendsto (fun β : ℝ => softMinMax β x) Filter.atTop (nhds (minMax x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (g := fun β : ℝ => Real.log (Fintype.card I : ℝ) / β +
    Real.log (Fintype.card J : ℝ) / β)
    (Filter.Eventually.of_forall (fun β => norm_nonneg _)) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with β hβ
    simpa only [Real.norm_eq_abs] using abs_softMinMax_sub_minMax_le β hβ x
  · have hI : Filter.Tendsto (fun β : ℝ => Real.log (Fintype.card I : ℝ) / β)
        Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop Filter.tendsto_id
    have hJ : Filter.Tendsto (fun β : ℝ => Real.log (Fintype.card J : ℝ) / β)
        Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop Filter.tendsto_id
    simpa only [add_zero] using hI.add hJ

#print axioms minMax_sub_log_card_le_softMinMax_le
#print axioms abs_softMinMax_sub_minMax_le
#print axioms abs_softMinMax_le_sum_abs_add_logs
#print axioms tendsto_softMinMax

end BMGordonSoftMinMax
