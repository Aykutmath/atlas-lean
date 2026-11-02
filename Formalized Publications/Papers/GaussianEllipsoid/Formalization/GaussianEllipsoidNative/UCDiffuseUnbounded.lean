import UCDiffuseUniform

/-! Removing the nuisance-radius restriction using the proved continuity
bound. The resulting bad event is open, making later Gaussian head/tail
conditioning independent of any measurable choice of nets or bases. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Module
open scoped BigOperators Topology
namespace GaussianEllipsoid.UCDiffuseUnbounded
open UCDiffuseActualBound UCDiffuseFiniteModel UCUniformContinuity UCContinuityGeometry

 def uncappedDiffuseBad (d n : ℕ) (τ c : ℝ)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Set (Sample d n) :=
  {x | ∃ A ∈ sourceDiffuseClass d τ, ∃ v : EuclideanSpace ℝ (Fin n),
    v ∈ L ∧ (1/(n:ℝ))*∑ i, |measurementQ x A i-v i| < c}

 theorem norm_le_sum_abs {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : ‖v‖ ≤ ∑ i, |v i| := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have he : (∑ i, v i • b i) = v := by simpa only [b, EuclideanSpace.basisFun_repr] using b.sum_repr v
  calc
    ‖v‖ = ‖∑ i, v i • b i‖ := congrArg norm he.symm
    _ ≤ ∑ i, ‖v i • b i‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, b.norm_eq_one, Real.norm_eq_abs]

/-- Pointwise reduction of an arbitrary low-residual nuisance vector to the
fixed-radius class on the actual continuity event. -/
theorem uncapped_bad_subset {d n : ℕ} (hn : 0 < n) (τ c C B : ℝ)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hB : C+c ≤ B) :
    uncappedDiffuseBad d n τ c L ⊆ {x | C < ‖empiricalOperator x‖} ∪ diffuseBad d n τ B c L := by
  rintro x ⟨A,hA,v,hv,hbad⟩
  by_cases hC : C < ‖empiricalOperator x‖
  · exact Or.inl hC
  have hC' := le_of_not_gt hC
  have hQ := empirical_mean_le_operator x A (psd_transpose hA.1)
  rw [hA.2.1,mul_one] at hQ
  have hsum : (1/(n:ℝ))*∑ i, |v i| ≤
      (1/(n:ℝ))*∑ i, |measurementQ x A i| + (1/(n:ℝ))*∑ i, |measurementQ x A i-v i| := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    have h := abs_sub (measurementQ x A i) (measurementQ x A i-v i)
    simpa only [sub_sub_cancel] using h
  have hvavg : (1/(n:ℝ))*∑ i, |v i| ≤ B := by linarith
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hvsum : (∑ i, |v i|) ≤ B*n := (div_le_iff₀ hnR).mp (by
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using hvavg)
  exact Or.inr ⟨A,hA,v,hv,(norm_le_sum_abs v).trans hvsum,hbad⟩

/-- The unbounded-nuisance bad event is an open union of continuous strict
residual sublevel sets, even though the nuisance parameter set is unbounded. -/
theorem isOpen_uncappedDiffuseBad (d n : ℕ) (τ c : ℝ)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : IsOpen (uncappedDiffuseBad d n τ c L) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨A,hA,v,hv,hbad⟩
  have hc : Continuous (fun y : Sample d n => (1/(n:ℝ))*∑ i, |measurementQ y A i-v i|) := by
    unfold measurementQ quadratic
    fun_prop
  have ho := isOpen_lt hc (continuous_const : Continuous (fun _ : Sample d n => c))
  apply Filter.mem_of_superset (ho.mem_nhds hbad)
  intro y hy
  exact ⟨A,hA,v,hv,hy⟩

 theorem measurableSet_uncappedDiffuseBad (d n : ℕ) (τ c : ℝ)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : MeasurableSet (uncappedDiffuseBad d n τ c L) :=
  (isOpen_uncappedDiffuseBad d n τ c L).measurableSet

/-- A fixed sum of two positive quadratic exponential rates has a positive
quadratic rate after an eventual constant-factor absorption. -/
theorem quadratic_exp_pair (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      Real.exp (-A*(d:ℝ)^2)+Real.exp (-B*(d:ℝ)^2) ≤ Real.exp (-C*(d:ℝ)^2) := by
  let k := min A B
  have hk : 0 < k := lt_min hA hB
  refine ⟨k/2,by positivity,?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2*Real.log 2/k),
    eventually_ge_atTop 1] with d hd hd1
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd1
  have hsq : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hlog : Real.log 2 ≤ k*(d:ℝ)^2/2 := by
    have h := (div_le_iff₀ hk).mp hd
    nlinarith [mul_le_mul_of_nonneg_left hsq hk.le]
  have heA : Real.exp (-A*(d:ℝ)^2) ≤ Real.exp (-k*(d:ℝ)^2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right (min_le_left A B) (sq_nonneg (d:ℝ))])
  have heB : Real.exp (-B*(d:ℝ)^2) ≤ Real.exp (-k*(d:ℝ)^2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right (min_le_right A B) (sq_nonneg (d:ℝ))])
  calc
    _ ≤ 2*Real.exp (-k*(d:ℝ)^2) := by linarith
    _ = Real.exp (Real.log 2-k*(d:ℝ)^2) := by
      rw [Real.exp_sub,Real.exp_log (by norm_num),
        show -k*(d:ℝ)^2=-(k*(d:ℝ)^2) by ring, Real.exp_neg]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- Unconditional full diffuse theorem with no nuisance-size restriction.
Its constants are independent of fixed nuisance rank M. -/
theorem uniform_diffuse_unbounded (αm αp : ℝ) (hαm : 1/4 < αm) (hαp : αm ≤ αp) :
    ∃ τ c C : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ M : ℕ, ∀ᶠ d : ℕ in atTop, ∀ n : ℕ,
        αm*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ αp*(d:ℝ)^2 →
        ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), finrank ℝ L ≤ M →
          (gaussianSampleLaw d n).real (uncappedDiffuseBad d n τ c L) ≤ Real.exp (-C*(d:ℝ)^2) := by
  obtain ⟨τ,c,C0,hτ,hτ1,hc,hC0,hBound⟩ := UCDiffuseUniform.uniform_diffuse_bound αm αp hαm hαp
  obtain ⟨C,hC,hPair⟩ := quadratic_exp_pair (1/4) C0 (by norm_num) hC0
  let Ccont := continuityConstant (1/4)
  have hCcont : 0 < Ccont := continuityConstant_pos (by norm_num)
  refine ⟨τ,c,C,hτ,hτ1,hc,hC,?_⟩
  intro M
  filter_upwards [hBound M (Ccont+c) (by positivity),hPair,eventually_ge_atTop 1] with d hd hdPair hd1
  intro n hnlo hnhi L hL
  have hdpos : 0 < d := by omega
  have hquarter : (1/4:ℝ)*(d:ℝ)^2 ≤ n :=
    (mul_le_mul_of_nonneg_right hαm.le (sq_nonneg (d:ℝ))).trans hnlo
  have hnR : (0:ℝ) < n := by
    have hdR : (0:ℝ) < d := by exact_mod_cast hdpos
    nlinarith [sq_pos_of_pos hdR]
  have hn : 0 < n := by exact_mod_cast hnR
  have hsub := uncapped_bad_subset (d := d) hn τ c Ccont (Ccont+c) L le_rfl
  have hcont := (empiricalOperator_tail (a := 1/4) (by norm_num) hdpos hn hquarter).trans
    (Real.exp_le_exp.mpr (by linarith : -(n:ℝ) ≤ -(1/4)*(d:ℝ)^2))
  have hb := hd n hnlo hnhi L hL
  calc
    _ ≤ (gaussianSampleLaw d n).real ({x | Ccont < ‖empiricalOperator x‖} ∪ diffuseBad d n τ (Ccont+c) c L) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (gaussianSampleLaw d n).real {x | Ccont < ‖empiricalOperator x‖} +
        (gaussianSampleLaw d n).real (diffuseBad d n τ (Ccont+c) c L) := measureReal_union_le _ _
    _ ≤ Real.exp (-(1/4)*(d:ℝ)^2)+Real.exp (-C0*(d:ℝ)^2) := add_le_add hcont hb
    _ ≤ _ := hdPair

#print axioms uniform_diffuse_unbounded
#print axioms measurableSet_uncappedDiffuseBad
end GaussianEllipsoid.UCDiffuseUnbounded
