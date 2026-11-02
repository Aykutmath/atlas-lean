import AHHNormalizedExpectationEndpoint
import GaussianDisjointSamples

/-! Finite Gaussian augmentation on the actual four-real product probability space.
The original sample is a literal prefix of the larger iid sample. An integer
auxiliary aspect gives an integral augmented sample count in every dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments AHHAlgebraBridges
open GaussianEllipsoid.ProjectedClusters
open Filter Asymptotics
open scoped BigOperators Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace AHHGaussian

/-- Literal initial-segment embedding, including the empty prefix. -/
def prefixEmbedding {n N : ℕ} (hn : n ≤ N) : Fin n ↪ Fin N :=
  ⟨Fin.castLE hn, Fin.castLE_injective hn⟩

/-- The remaining N-n samples, in their original order. -/
def suffixEmbedding {n N : ℕ} (hn : n ≤ N) : Fin (N-n) ↪ Fin N where
  toFun i := ⟨n+i.val, by omega⟩
  inj' := by intro i j hij; apply Fin.ext; have := congrArg Fin.val hij; dsimp at this; omega

theorem prefix_suffix_disjoint {n N : ℕ} (hn : n ≤ N)
    (i : Fin n) (j : Fin (N-n)) : prefixEmbedding hn i ≠ suffixEmbedding hn j := by
  intro hij
  have he := congrArg Fin.val hij
  change i.val = n+j.val at he
  omega

/-- Select all four real arrays along the same sample embedding. -/
def selectFour {n N h : ℕ} (e : Fin n ↪ Fin N) (x : FourEntries N h) : FourEntries n h :=
  (selectSample e x.1, selectSample e x.2)

theorem selectFour_preserving {n N h : ℕ} (e : Fin n ↪ Fin N) :
    MeasurePreserving (selectFour (h := h) e) (fourGaussianLaw N h) (fourGaussianLaw n h) :=
  (selectSample_preserving e).prod (selectSample_preserving e)

/-- Exact law of the finite original Gaussian prefix, without any law hypothesis. -/
theorem fourGaussianLaw_map_prefix {n N h : ℕ} (hn : n ≤ N) :
    (fourGaussianLaw N h).map (selectFour (h := h) (prefixEmbedding hn)) =
      fourGaussianLaw n h := (selectFour_preserving _).map_eq

@[simp] theorem actualProductStates_selectFour {n N h : ℕ} (e : Fin n ↪ Fin N)
    (s t : Bool) (x : FourEntries N h) (i : Fin n) :
    actualProductStates n h s t (selectFour e x) i = actualProductStates N h s t x (e i) := rfl

/-- Regroup four independent variables, retaining the exact product measure. -/
private theorem regroup_preserving {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun z : (α × β) × (γ × δ) => ((z.1.1,z.2.1),(z.1.2,z.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have hswap := (measurePreserving_prodAssoc μc μb μd).comp
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have hmiddle := hswap.comp (measurePreserving_prodAssoc μb μc μd).symm
  exact (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm.comp
    (((MeasurePreserving.id μa).prod hmiddle).comp
      (measurePreserving_prodAssoc μa μb (μc.prod μd)))

/-- Disjoint selections of all four arrays have the product of their exact laws. -/
theorem disjointFour_preserving {n p N h : ℕ} (e : Fin n ↪ Fin N) (f : Fin p ↪ Fin N)
    (hd : ∀ i j, e i ≠ f j) :
    MeasurePreserving (fun x : FourEntries N h => (selectFour e x, selectFour f x))
      (fourGaussianLaw N h) ((fourGaussianLaw n h).prod (fourGaussianLaw p h)) := by
  exact (regroup_preserving (pairGaussianLaw n h) (pairGaussianLaw p h)
    (pairGaussianLaw n h) (pairGaussianLaw p h)).comp
      ((disjointSamples_preserving e f hd).prod (disjointSamples_preserving e f hd))

/-- In particular, the suffix is an independent fresh Gaussian sample of size N-n. -/
theorem fourGaussianLaw_map_prefix_suffix {n N h : ℕ} (hn : n ≤ N) :
    (fourGaussianLaw N h).map (fun x =>
      (selectFour (h := h) (prefixEmbedding hn) x, selectFour (suffixEmbedding hn) x)) =
        (fourGaussianLaw n h).prod (fourGaussianLaw (N-n) h) :=
  (disjointFour_preserving _ _ (prefix_suffix_disjoint hn)).map_eq

theorem selectFour_indepFun {n p N h : ℕ} (e : Fin n ↪ Fin N) (f : Fin p ↪ Fin N)
    (hd : ∀ i j, e i ≠ f j) :
    IndepFun (selectFour (h := h) e) (selectFour f) (fourGaussianLaw N h) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (selectFour_preserving e).measurable.aemeasurable
    (selectFour_preserving f).measurable.aemeasurable).mpr
  rw [(selectFour_preserving e).map_eq, (selectFour_preserving f).map_eq]
  exact (disjointFour_preserving e f hd).map_eq

/-- Independence of the actual original and additional normalized product states,
proved from the four-real Gaussian law rather than assumed in the statement. -/
theorem actualProductStates_prefix_suffix_indepFun {n N h : ℕ} (hn : n ≤ N)
    (s t : Bool) :
    IndepFun
      (fun x => actualProductStates n h s t (selectFour (prefixEmbedding hn) x))
      (fun x => actualProductStates (N-n) h s t (selectFour (suffixEmbedding hn) x))
      (fourGaussianLaw N h) := by
  refine (selectFour_indepFun (h := h) (prefixEmbedding hn) (suffixEmbedding hn)
    (prefix_suffix_disjoint hn)).comp
      (φ := actualProductStates n h s t) (ψ := actualProductStates (N-n) h s t) ?_ ?_
  all_goals
    unfold actualProductStates fourRealRows pairRealRows
    exact measurable_pi_iff.mpr (fun i => (measurable_normalizedProductRow h s t).comp (by fun_prop))

/-- The selected states retain the exact iid normalized complex Gaussian row law. -/
theorem selected_actualProductStates_joint_law {n N h : ℕ} (e : Fin n ↪ Fin N)
    (s t : Bool) :
    (fourGaussianLaw N h).map (fun x => actualProductStates n h s t (selectFour e x)) =
      Measure.pi (fun _ : Fin n => complexProductStateLaw h s t) := by
  have hm : Measurable (actualProductStates n h s t) := by
    unfold actualProductStates fourRealRows pairRealRows
    exact measurable_pi_iff.mpr (fun i => (measurable_normalizedProductRow h s t).comp (by fun_prop))
  rw [show (fun x => actualProductStates n h s t (selectFour e x)) =
    actualProductStates n h s t ∘ selectFour e from rfl,
    ← Measure.map_map hm (selectFour_preserving e).measurable,
    (selectFour_preserving e).map_eq, actualProductStates_joint_law]

/-- The smaller covariance is the literal PSD subsum of the augmented covariance. -/
theorem actualComplexCovariance_selectFour_le {n N h : ℕ} (e : Fin n ↪ Fin N)
    (s t : Bool) (x : FourEntries N h) :
    actualComplexCovariance n h s t (selectFour e x) ≤ actualComplexCovariance N h s t x := by
  classical
  simp only [actualComplexCovariance_eq_sum_projectors, actualProductStates_selectFour]
  exact Finset.sum_le_sum_of_injOn e e.injective.injOn (Finset.subset_univ _)
    (fun _ _ => le_rfl) (fun _ _ _ => (projector_posSemidef _).nonneg)

/-- Augmentation literally adds the covariance of the independent suffix. -/
theorem actualComplexCovariance_prefix_add_suffix {n N h : ℕ} (hn : n ≤ N)
    (s t : Bool) (x : FourEntries N h) :
    actualComplexCovariance N h s t x =
      actualComplexCovariance n h s t (selectFour (prefixEmbedding hn) x) +
      actualComplexCovariance (N-n) h s t (selectFour (suffixEmbedding hn) x) := by
  classical
  let f : Fin n ⊕ Fin (N-n) → Fin N := Sum.elim (prefixEmbedding hn) (suffixEmbedding hn)
  have hf : Function.Bijective f := by
    refine ⟨(prefixEmbedding hn).injective.sumElim (suffixEmbedding hn).injective
      (prefix_suffix_disjoint hn), ?_⟩
    intro i
    by_cases hi : i.val < n
    · exact ⟨Sum.inl ⟨i.val, hi⟩, Fin.ext rfl⟩
    · refine ⟨Sum.inr ⟨i.val-n, by omega⟩, ?_⟩
      apply Fin.ext
      change n + (i.val-n) = i.val
      omega
  have he := Fintype.sum_equiv (Equiv.ofBijective f hf)
    (fun k => projector (fun p => actualProductStates N h s t x (f k) p))
    (fun i => projector (fun p => actualProductStates N h s t x i p)) (fun _ => rfl)
  rw [Fintype.sum_sum_type] at he
  simpa only [actualComplexCovariance_eq_sum_projectors, actualProductStates_selectFour,
    f, Sum.elim_inl, Sum.elim_inr] using he.symm

/-- Monotonicity is for the genuine complex Euclidean operator norm. -/
theorem actualComplexCovariance_selectFour_norm_le {n N h : ℕ} (e : Fin n ↪ Fin N)
    (s t : Bool) (x : FourEntries N h) :
    ‖cMatrixCLM (actualComplexCovariance n h s t (selectFour e x))‖ ≤
      ‖cMatrixCLM (actualComplexCovariance N h s t x)‖ := by
  simp only [cMatrixCLM_norm]
  refine CStarAlgebra.norm_le_norm_of_le_of_nonneg (actualComplexCovariance_selectFour_le e s t x) ?_
  rw [actualComplexCovariance_eq_sum_projectors]
  exact Finset.sum_nonneg (fun _ _ => (projector_posSemidef _).nonneg)

theorem actualComplexCovariance_norm_measurable (n h : ℕ) (s t : Bool) :
    Measurable (fun x => ‖cMatrixCLM (actualComplexCovariance n h s t x)‖) := by
  have hm : Continuous (actualComplexCovariance n h s t) := by
    unfold actualComplexCovariance complexCov projector productState pureTensor complexFactor
    fun_prop
  exact (((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin h × Fin h) (n := Fin h × Fin h)).trans
    LinearMap.toContinuousLinearMap).toLinearMap.continuous_of_finiteDimensional.comp hm).norm.measurable

/-- Tail probabilities are dominated after transporting through the exact prefix law. -/
theorem actualComplexCovariance_tail_mono {n N h : ℕ} (hn : n ≤ N) (s t : Bool) (a : ℝ) :
    (fourGaussianLaw n h).real {x | a < ‖cMatrixCLM (actualComplexCovariance n h s t x)‖} ≤
      (fourGaussianLaw N h).real {x | a < ‖cMatrixCLM (actualComplexCovariance N h s t x)‖} := by
  have hm := map_measureReal_apply (μ := fourGaussianLaw N h)
    (s := {x | a < ‖cMatrixCLM (actualComplexCovariance n h s t x)‖})
    (selectFour_preserving (h := h) (prefixEmbedding hn)).measurable
    (measurableSet_lt measurable_const (actualComplexCovariance_norm_measurable n h s t))
  rw [fourGaussianLaw_map_prefix] at hm
  rw [hm]
  exact measureReal_mono (fun x hx =>
    hx.trans_le (actualComplexCovariance_selectFour_norm_le (prefixEmbedding hn) s t x))

/-- Expected norms are monotone in the finite number of iid samples. -/
theorem actualComplexCovariance_expected_norm_mono {n N h : ℕ} (hn : n ≤ N)
    (hh : 0 < h) (s t : Bool) :
    (∫ x, ‖cMatrixCLM (actualComplexCovariance n h s t x)‖ ∂fourGaussianLaw n h) ≤
      ∫ x, ‖cMatrixCLM (actualComplexCovariance N h s t x)‖ ∂fourGaussianLaw N h := by
  have hp := selectFour_preserving (h := h) (prefixEmbedding hn)
  have hi := AHHRadial.actualComplexCovariance_norm_integrable n h hh s t
  have hm := integral_map (μ := fourGaussianLaw N h) hp.measurable.aemeasurable
    (actualComplexCovariance_norm_measurable n h s t).aestronglyMeasurable
  rw [hp.map_eq] at hm
  rw [hm]
  exact integral_mono (hp.integrable_comp_of_integrable hi)
    (AHHRadial.actualComplexCovariance_norm_integrable N h hh s t)
    (actualComplexCovariance_selectFour_norm_le (prefixEmbedding hn) s t)

/-- A natural auxiliary aspect can be chosen strictly above any finite real bound. -/
theorem exists_integer_auxiliary_aspect (A : ℝ) : ∃ x₀ : ℕ, 1 ≤ x₀ ∧ A < (x₀ : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_gt A
  exact ⟨k+1, by omega, hk.trans (by exact_mod_cast Nat.lt_succ_self k)⟩

/-- The augmented sample count is integral by construction. -/
def augmentedCount (x₀ h : ℕ) : ℕ := x₀*h^2

theorem le_augmentedCount {A : ℝ} {x₀ n h : ℕ} (hA : A ≤ (x₀ : ℝ))
    (hn : (n : ℝ) ≤ A*(h : ℝ)^2) : n ≤ augmentedCount x₀ h := by
  have hb := hn.trans (mul_le_mul_of_nonneg_right hA (sq_nonneg (h : ℝ)))
  exact_mod_cast hb

/-- Positive dimensions have exactly the selected auxiliary aspect, with no rounding error. -/
theorem augmentedCount_aspect (x₀ h : ℕ) (hh : 0 < h) :
    (augmentedCount x₀ h : ℝ)/(h : ℝ)^2 = (x₀ : ℝ) := by
  simp only [augmentedCount, Nat.cast_mul, Nat.cast_pow]
  exact mul_div_cancel_right₀ _ (by positivity)

theorem augmentedCount_aspect_tendsto (x₀ : ℕ) :
    Tendsto (fun h : ℕ => (augmentedCount x₀ h : ℝ)/(h : ℝ)^2) atTop (𝓝 (x₀ : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with h hh
  exact (augmentedCount_aspect x₀ h (by omega)).symm

/-- Apply the actual sharp Gaussian edge to the integral augmented family and
then dominate the original bounded-aspect family through its exact prefix law. -/
theorem bounded_aspect_expected_norm_via_augmentation (p : ℕ → ℕ) (A : ℝ)
    (hp : ∀ h, (p h : ℝ) ≤ A*(h : ℝ)^2) :
    ∃ x₀ : ℕ, 1 ≤ x₀ ∧ A < (x₀ : ℝ) ∧
      (∀ h, p h ≤ augmentedCount x₀ h) ∧
      (∀ h, 0 ≤ AHH.edgeError (augmentedCount x₀) (x₀ : ℝ) h) ∧
      AHH.edgeError (augmentedCount x₀) (x₀ : ℝ) =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ (h : ℕ) (s t : Bool),
        (∫ z, ‖cMatrixCLM (actualComplexCovariance (p h) h s t z)‖ ∂fourGaussianLaw (p h) h) ≤
          (1 + Real.sqrt (x₀ : ℝ))^2 + AHH.edgeError (augmentedCount x₀) (x₀ : ℝ) h := by
  obtain ⟨x₀, hx, hA⟩ := exists_integer_auxiliary_aspect A
  have hc : ∀ h, p h ≤ augmentedCount x₀ h := fun h => le_augmentedCount hA.le (hp h)
  have he := normalizedGaussian_all_signs_expectation_upper_edge (augmentedCount x₀)
    (by exact_mod_cast (show 0 < x₀ by omega)) (augmentedCount_aspect_tendsto x₀)
  refine ⟨x₀, hx, hA, hc, he.1, he.2.1, ?_⟩
  intro h s t
  by_cases hh : 0 < h
  · exact (actualComplexCovariance_expected_norm_mono (hc h) hh s t).trans (he.2.2 h s t)
  · have hz : h = 0 := by omega
    subst h
    rw [actualGaussian_expected_norm_zero]
    exact add_nonneg (sq_nonneg _) (AHH.edgeError_nonneg _ _ _)

/-- Bounded aspect ratios need only be controlled at positive dimensions; no
condition on the irrelevant zero-dimensional sample count is imposed. -/
theorem bounded_ratio_expected_norm_via_augmentation (p : ℕ → ℕ) (A : ℝ)
    (hp : ∀ h, 0 < h → (p h : ℝ)/(h : ℝ)^2 ≤ A) :
    ∃ x₀ : ℕ, 1 ≤ x₀ ∧ A < (x₀ : ℝ) ∧
      (∀ h, 0 < h → p h ≤ augmentedCount x₀ h ∧
        (augmentedCount x₀ h : ℝ)/(h : ℝ)^2 = (x₀ : ℝ)) ∧
      (∀ h, 0 ≤ AHH.edgeError (augmentedCount x₀) (x₀ : ℝ) h) ∧
      AHH.edgeError (augmentedCount x₀) (x₀ : ℝ) =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ (h : ℕ) (s t : Bool),
        (∫ z, ‖cMatrixCLM (actualComplexCovariance (p h) h s t z)‖ ∂fourGaussianLaw (p h) h) ≤
          (1 + Real.sqrt (x₀ : ℝ))^2 + AHH.edgeError (augmentedCount x₀) (x₀ : ℝ) h := by
  obtain ⟨x₀, hx, hA⟩ := exists_integer_auxiliary_aspect A
  have hc : ∀ h, 0 < h → p h ≤ augmentedCount x₀ h := by
    intro h hh
    exact le_augmentedCount hA.le ((div_le_iff₀ (by positivity)).mp (hp h hh))
  have he := normalizedGaussian_all_signs_expectation_upper_edge (augmentedCount x₀)
    (by exact_mod_cast (show 0 < x₀ by omega)) (augmentedCount_aspect_tendsto x₀)
  refine ⟨x₀, hx, hA, (fun h hh => ⟨hc h hh, augmentedCount_aspect x₀ h hh⟩),
    he.1, he.2.1, ?_⟩
  intro h s t
  by_cases hh : 0 < h
  · exact (actualComplexCovariance_expected_norm_mono (hc h hh) hh s t).trans (he.2.2 h s t)
  · have hz : h = 0 := by omega
    subst h
    rw [actualGaussian_expected_norm_zero]
    exact add_nonneg (sq_nonneg _) (AHH.edgeError_nonneg _ _ _)

#print axioms fourGaussianLaw_map_prefix
#print axioms fourGaussianLaw_map_prefix_suffix
#print axioms selected_actualProductStates_joint_law
#print axioms actualProductStates_prefix_suffix_indepFun
#print axioms actualComplexCovariance_prefix_add_suffix
#print axioms actualComplexCovariance_selectFour_norm_le
#print axioms actualComplexCovariance_tail_mono
#print axioms actualComplexCovariance_expected_norm_mono
#print axioms augmentedCount_aspect
#print axioms bounded_ratio_expected_norm_via_augmentation

end AHHGaussian
