import GaussianChiSquareTail
import ActualCoefficientNets
import SparsePrefixSynthesis

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoid
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoidCandidate

/-- The rank-one dual pairing is the actual Euclidean bilinear pairing. -/
theorem bilinearRowOperator_pairing {r q : ℕ} (p : Euclid q × Euclid r)
    (W : Euclid q →L[ℝ] Euclid r) :
    ⟪operatorFrobenius (bilinearRowOperator p), operatorFrobenius W⟫_ℝ =
      ⟪p.2, W p.1⟫_ℝ := by
  rw [← sum_inner_operator_basis _ _ (EuclideanSpace.basisFun (Fin q) ℝ)]
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin q) ℝ).sum_repr' p.1]
  simp only [bilinearRowOperator_apply, real_inner_smul_left, map_sum, map_smul,
    inner_sum, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm p.1]

/-- Nuclear norm of an actual Gaussian rank-one row has the expected product upper bound. -/
theorem bilinearRowOperator_nuclear_le {r q : ℕ} (p : Euclid q × Euclid r) :
    spectralNuclearNorm (operatorFrobenius (bilinearRowOperator p)) ≤ ‖p.1‖ * ‖p.2‖ := by
  apply (spectralNuclear_le_iff _ _).mpr
  intro W hW
  rw [bilinearRowOperator_pairing]
  calc
    ⟪p.2, W p.1⟫_ℝ ≤ ‖p.2‖ * ‖W p.1‖ := real_inner_le_norm _ _
    _ ≤ ‖p.2‖ * (‖W‖ * ‖p.1‖) :=
      mul_le_mul_of_nonneg_left (W.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖p.2‖ * (1 * ‖p.1‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- Each pair coordinate has exactly its independent two-factor Gaussian law. -/
theorem gaussianBilinearSampleLaw_coordinate {ι : Type*} [Fintype ι]
    (q r : ℕ) (i : ι) :
    (gaussianBilinearSampleLaw ι q r).map (fun X => X i) =
      (euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r)) := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have heq : (fun X : ι → Euclid q × Euclid r => X i) ⁻¹' s =
      Set.univ.pi (fun j : ι => if j=i then s else Set.univ) := by ext X; simp
  rw [heq, gaussianBilinearSampleLaw, Measure.pi_pi]
  simp_rw [apply_ite]
  simp

/-- Chi-square upper tail in the actual Euclidean Gaussian law. -/
theorem euclideanGaussian_norm_sq_upper (h : ℕ) :
    (euclideanGaussianLaw (Fin h)).real {x | (5/4 : ℝ)*h ≤ ‖x‖^2} ≤
      Real.exp (-(h : ℝ)/256) := by
  have hs : MeasurableSet {x : Euclid h | (5/4 : ℝ)*h ≤ ‖x‖^2} := measurableSet_le measurable_const (by fun_prop)
  unfold euclideanGaussianLaw Measure.real
  rw [Measure.map_apply (MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).measurable hs]
  have heq : (MeasurableEquiv.toLp 2 ((Fin h) → ℝ)) ⁻¹'
      {x : Euclid h | (5/4 : ℝ)*h ≤ ‖x‖^2} =
      {x : Fin h → ℝ | (5/4 : ℝ)*h ≤ ∑ i, (x i)^2} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  rw [heq]
  simpa only [Fintype.card_fin, Measure.real] using gaussian_square_sum_upper (ι := Fin h)

/-- The atom event is a Borel condition on all the actual Gaussian rows. -/
def atomRowsGood (d n h : ℕ) : Set (Fin n → Euclid h × Euclid h) :=
  {X | ∀ i, ‖(X i).1‖^2 ≤ d ∧ ‖(X i).2‖^2 ≤ d}

theorem atomRowsGood_measurable (d n h : ℕ) : MeasurableSet (atomRowsGood d n h) := by
  unfold atomRowsGood
  simp only [Set.setOf_forall, Set.setOf_and]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)

/-- Actual-law atom failure bound. It costs only 2n scalar-vector tail events. -/
theorem atomRowsGood_failure_le (d n h : ℕ) (hdh : (5/4 : ℝ)*h ≤ d) :
    (gaussianBilinearSampleLaw (Fin n) h h).real (atomRowsGood d n h)ᶜ ≤
      2*n*Real.exp (-(h : ℝ)/256) := by
  let E : Set (Euclid h) := {x | (5/4 : ℝ)*h ≤ ‖x‖^2}
  have hE : MeasurableSet E := measurableSet_le measurable_const (by fun_prop)
  let F : Set (Euclid h × Euclid h) := Prod.fst ⁻¹' E ∪ Prod.snd ⁻¹' E
  have hF : MeasurableSet F := (hE.preimage measurable_fst).union (hE.preimage measurable_snd)
  have hpair : ((euclideanGaussianLaw (Fin h)).prod (euclideanGaussianLaw (Fin h))).real F ≤
      2*Real.exp (-(h:ℝ)/256) := by
    have hf : ((euclideanGaussianLaw (Fin h)).prod (euclideanGaussianLaw (Fin h))).real
        (Prod.fst ⁻¹' E) = (euclideanGaussianLaw (Fin h)).real E := by
      rw [Measure.real, ← Measure.map_apply measurable_fst hE, Measure.map_fst_prod]
      simp [Measure.real]
    have hs : ((euclideanGaussianLaw (Fin h)).prod (euclideanGaussianLaw (Fin h))).real
        (Prod.snd ⁻¹' E) = (euclideanGaussianLaw (Fin h)).real E := by
      rw [Measure.real, ← Measure.map_apply measurable_snd hE, Measure.map_snd_prod]
      simp [Measure.real]
    apply (measureReal_union_le _ _).trans
    rw [hf, hs]
    linarith [euclideanGaussian_norm_sq_upper h]
  have hrow (i : Fin n) : (gaussianBilinearSampleLaw (Fin n) h h).real
      ((fun X => X i) ⁻¹' F) ≤ 2*Real.exp (-(h:ℝ)/256) := by
    rw [Measure.real, ← Measure.map_apply (measurable_pi_apply i) hF,
      gaussianBilinearSampleLaw_coordinate]
    exact hpair
  have hsub : (atomRowsGood d n h)ᶜ ⊆ ⋃ i : Fin n, (fun X => X i) ⁻¹' F := by
    intro X hX
    simp only [atomRowsGood, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_and_or,
      not_le] at hX
    obtain ⟨i, hi⟩ := hX
    apply Set.mem_iUnion.mpr ⟨i, ?_⟩
    rcases hi with hi | hi
    · exact Or.inl (hdh.trans hi.le)
    · exact Or.inr (hdh.trans hi.le)
  calc
    _ ≤ (gaussianBilinearSampleLaw (Fin n) h h).real
      (⋃ i : Fin n, (fun X => X i) ⁻¹' F) := measureReal_mono hsub
    _ ≤ ∑ i : Fin n, (gaussianBilinearSampleLaw (Fin n) h h).real
      ((fun X => X i) ⁻¹' F) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, 2*Real.exp (-(h:ℝ)/256) := Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp; ring

theorem atomRowsGood_row_bound {d n h : ℕ} {X : Fin n → Euclid h × Euclid h}
    (hX : X ∈ atomRowsGood d n h) (i : Fin n) :
    spectralNuclearNorm (operatorFrobenius
      ((Real.sqrt (d:ℝ))⁻¹ • bilinearRowOperator (X i))) ≤ Real.sqrt d := by
  have hleft : ‖(X i).1‖ ≤ Real.sqrt d :=
    (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).mpr (hX i).1
  have hright : ‖(X i).2‖ ≤ Real.sqrt d :=
    (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).mpr (hX i).2
  have hprod : ‖(X i).1‖*‖(X i).2‖ ≤ (d:ℝ) := by
    calc _ ≤ Real.sqrt d * Real.sqrt d := mul_le_mul hleft hright (norm_nonneg _) (Real.sqrt_nonneg _)
         _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [GaussianEllipsoid.SparseSupport.operatorFrobenius_smul_eq, spectralNuclear_smul,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    _ ≤ (Real.sqrt (d:ℝ))⁻¹ * (d:ℝ) :=
      mul_le_mul_of_nonneg_left ((bilinearRowOperator_nuclear_le _).trans hprod) (by positivity)
    _ = Real.sqrt d := by
      by_cases hd : d = 0
      · simp [hd]
      · have hs : Real.sqrt (d:ℝ) ≠ 0 := by positivity
        rw [← Real.sq_sqrt (Nat.cast_nonneg d)]
        field_simp
        simp only [Real.sq_sqrt (sq_nonneg _)]

end GaussianEllipsoidCandidate
