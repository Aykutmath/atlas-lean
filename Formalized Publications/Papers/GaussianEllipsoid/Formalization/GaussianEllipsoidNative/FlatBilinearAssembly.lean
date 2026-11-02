import MixedNormDeterministic

noncomputable section
set_option synthInstance.maxSize 1000
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoid.Localized
open GaussianMixedNormHelpers GaussianEllipsoidFinalPassage
open GaussianTensorMoments GaussianBilinearTransport GaussianEllipsoidCandidate
open scoped BigOperators Topology
namespace GaussianEllipsoidStandalone

theorem flat_bilinear_eq_canonical (n r d : ℕ)
    (z : GaussianEntries n r × GaussianEntries n r) (y : Coeff n) :
    gaussianBilinearOperator n r d z y =
      operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ •
        bilinearSynthesis (fun i => y i) (tensorToCanonicalRows n r z)) := by
  ext j i
  change frobeniusToMatrix (gaussianBilinearOperator n r d z y) i j = _
  rw [gaussianBilinearOperator_apply]
  change _ = (Real.sqrt (d:ℝ))⁻¹ * operatorFrobenius
    (bilinearSynthesis (fun i => y i) (tensorToCanonicalRows n r z)) j i
  rw [bilinearSynthesis_entry]
  rfl

theorem localized_flatToSmallBall_eq (n r d : ℕ) (hr : 0 < r)
    (z : GaussianEntries n r × GaussianEntries n r) (y : Coeff n) :
    localizedOperator d r n (flatToSmallBall n r z) y = gaussianBilinearOperator n r d z y := by
  rw [localizedOperator_smallBallToFlat n r d hr, smallBallToFlat_flatToSmallBall]

def flatSmallBad (n r d : ℕ) (η c : ℝ) : Set (GaussianEntries n r × GaussianEntries n r) :=
  (flatToSmallBall n r) ⁻¹' homogeneousBad (localizedOperator d r n)
    (1/η) (2*η) 1 (1/η^2) c d

theorem flatSmallBad_measurable (n r d : ℕ) (η c : ℝ) :
    MeasurableSet (flatSmallBad n r d η c) :=
  (isOpen_homogeneousBad d r n (1/η) (2*η) 1 (1/η^2) c).measurableSet.preimage
    (flatToSmallBall_measurable n r)

theorem flatSmallBad_probability (n r d : ℕ) (η c : ℝ) :
    (tensorGaussianLaw n r).real (flatSmallBad n r d η c) =
      (GaussianEllipsoid.SmallBall.bilinearGaussianSampleLaw r n).real
        (homogeneousBad (localizedOperator d r n) (1/η) (2*η) 1 (1/η^2) c d) := by
  exact (flatToSmallBall_preserving n r).measureReal_preimage
    (isOpen_homogeneousBad d r n (1/η) (2*η) 1 (1/η^2) c).measurableSet.nullMeasurableSet

def flatContinuity (n r d : ℕ) : Set (GaussianEntries n r × GaussianEntries n r) :=
  {z | ‖gaussianBilinearOperator n r d z‖ ≤ 96 * Real.sqrt d}

theorem flatContinuity_measurable (n r d : ℕ) : MeasurableSet (flatContinuity n r d) := by
  have h := gaussianBilinearOperator_bad_measurableSet n r d 96
  convert h.compl using 1
  ext z
  simp [flatContinuity]

/-- The actual small-coordinate estimate in the same flat Gaussian law as continuity. -/
theorem flat_small_probability_tendsto_zero {α η : ℝ}
    (hα : 0 < α) (hα' : α < 1/4) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n : ℕ → ℕ,
      (∀ᶠ d in atTop, (n d:ℝ) ≤ α*(d:ℝ)^2) →
      Tendsto (fun d => (tensorGaussianLaw (n d) (2*(d/4))).real
        (flatSmallBad (n d) (2*(d/4)) d η c)) atTop (𝓝 0) := by
  obtain ⟨c,hc,hc1,ht⟩ := exists_gaussian_localized_bad_probability_tendsto_zero
    hα hα' (by positivity : 0 < 1/η) (by norm_num : (0:ℝ) < 1)
    (by positivity : 0 < 2*η) (by positivity : 0 < 1/η^2)
  refine ⟨c,hc,hc1,fun n hn => ?_⟩
  simpa only [flatSmallBad_probability] using ht n hn

/-- The full continuity exceptional probability is negligible. -/
theorem flat_continuity_probability_tendsto_zero (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, n d ≤ d^2) :
    Tendsto (fun d => (tensorGaussianLaw (n d) (2*(d/4))).real
      (flatContinuity (n d) (2*(d/4)) d)ᶜ) atTop (𝓝 0) := by
  have heq : ∀ d, (flatContinuity (n d) (2*(d/4)) d)ᶜ =
      {z | 96*Real.sqrt d < ‖gaussianBilinearOperator (n d) (2*(d/4)) d z‖} := by
    intro d; ext z; simp [flatContinuity]
  simp_rw [heq]
  exact gaussianBilinearOperator_even_bad_probability_tendsto_zero n hn

/-- Canonical bad event for the exact infimal mixed norm. -/
def canonicalMixedBad (n r d : ℕ) (η c : ℝ) : Set (Fin n → Euclid r × Euclid r) :=
  {X | ∃ y : Fin n → ℝ, spectralNuclearNorm (operatorFrobenius
    ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis y X)) < c*mixedNorm η d n y}

theorem continuous_bilinearSynthesis (n r : ℕ) (y : Fin n → ℝ) :
    Continuous (bilinearSynthesis y : (Fin n → Euclid r × Euclid r) → _) := by
  unfold bilinearSynthesis
  apply continuous_finset_sum
  intro i hi
  exact ((continuous_bilinearRowOperator r r).comp (continuous_apply i)).const_smul (y i)

theorem canonicalMixedBad_isOpen (n r d : ℕ) (η c : ℝ) :
    IsOpen (canonicalMixedBad n r d η c) := by
  have heq : canonicalMixedBad n r d η c = ⋃ y : Fin n → ℝ,
      {X | spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis y X)) < c*mixedNorm η d n y} := by
    ext X; simp [canonicalMixedBad]
  rw [heq]
  apply isOpen_iUnion
  intro y
  apply isOpen_lt _ continuous_const
  exact (continuous_spectralNuclear r r).comp ((continuous_operatorFrobenius r r).comp
    (by simpa only [Pi.smul_apply] using!
      ((continuous_bilinearSynthesis n r y).const_smul ((Real.sqrt (d : ℝ))⁻¹))))

def flatMixedBad (n r d : ℕ) (η c : ℝ) : Set (GaussianEntries n r × GaussianEntries n r) :=
  {z | ∃ y : Fin n → ℝ, spectralNuclearNorm (gaussianBilinearOperator n r d z (asCoeff y)) <
    c*mixedNorm η d n y}

theorem flatMixedBad_eq_preimage (n r d : ℕ) (η c : ℝ) :
    flatMixedBad n r d η c =
      (tensorToCanonicalRows n r) ⁻¹' canonicalMixedBad n r d η c := by
  ext z
  simp only [flatMixedBad, canonicalMixedBad, Set.mem_setOf_eq, Set.mem_preimage]
  simp_rw [flat_bilinear_eq_canonical]
  rfl

theorem flatMixedBad_measurable (n r d : ℕ) (η c : ℝ) :
    MeasurableSet (flatMixedBad n r d η c) := by
  rw [flatMixedBad_eq_preimage]
  exact (canonicalMixedBad_isOpen n r d η c).measurableSet.preimage
    (tensorToCanonicalRows_preserving n r).measurable

theorem flatMixedBad_probability (n r d : ℕ) (η c : ℝ) :
    (tensorGaussianLaw n r).real (flatMixedBad n r d η c) =
      (gaussianBilinearSampleLaw (Fin n) r r).real (canonicalMixedBad n r d η c) := by
  rw [flatMixedBad_eq_preimage]
  exact (tensorToCanonicalRows_preserving n r).measureReal_preimage
    (canonicalMixedBad_isOpen n r d η c).measurableSet.nullMeasurableSet

/-- The quantitative head coefficient used at the fixed paper parameters. -/
def fixedHeadCoefficient : ℝ := (1/2:ℝ)^30 / numericalDlog

def fixedSparseCoefficient : ℝ := numericalEta * fixedHeadCoefficient

theorem fixed_head_nonneg : 0 ≤ fixedHeadCoefficient := by
  exact (div_pos (by norm_num) numerical_Dlog_bounds.1).le

theorem fixed_head_absorption :
    (1/2:ℝ)^39 ≤ fixedHeadCoefficient * (1-numericalBeta) - 96*numericalBeta := by
  apply numerical_full_absorption
  unfold fixedHeadCoefficient
  rw [div_mul_cancel₀ _ numerical_Dlog_bounds.1.ne']

def flatSparseBad (n r d : ℕ) : Set (GaussianEntries n r × GaussianEntries n r) :=
  {z | ∃ (I : Finset (Fin n)) (u : Coeff n),
    (I.card:ℝ) ≤ (d:ℝ)/numericalEta^2 ∧ (∀ i ∉ I, u i = 0) ∧
    spectralNuclearNorm (gaussianBilinearOperator n r d z u) <
      fixedSparseCoefficient * Real.sqrt d * (∑ i, |u i|)}

/-- All-vector failure is covered by the three explicitly defined bad events. -/
theorem flatMixedBad_subset {n r d : ℕ} (hd : 0 < d) (hr : 0 < r) (hrd : r ≤ d)
    {cS : ℝ} :
    flatMixedBad n r d numericalEta (min cS ((1/2:ℝ)^39)) ⊆
      (flatContinuity n r d)ᶜ ∪ flatSparseBad n r d ∪ flatSmallBad n r d numericalEta cS := by
  classical
  intro z hz
  by_cases hC : z ∈ flatContinuity n r d
  · by_cases hH : z ∈ flatSparseBad n r d
    · exact Or.inl (Or.inr hH)
    · by_cases hS : z ∈ flatSmallBad n r d numericalEta cS
      · exact Or.inr hS
      · exfalso
        obtain ⟨y,hy⟩ := hz
        have hb := mixed_lower_of_three_events hd hrd (localizedOperator d r n)
          numerical_eta_range.1 numerical_eta_range.2.1.le fixed_head_nonneg
          (flatToSmallBall n r z) ?_ ?_ hS y
        · have hmin : min cS ((1/2:ℝ)^39) ≤
              min cS (fixedHeadCoefficient*(1-2*numericalEta)-96*(2*numericalEta)) := by
            exact min_le_min_left _ fixed_head_absorption
          have hb' := (mul_le_mul_of_nonneg_right hmin
            (mixedNorm_nonneg numerical_eta_range.1.le d n y)).trans hb
          rw [localized_flatToSmallBall_eq n r d hr] at hb'
          exact (not_lt_of_ge hb') hy
        · intro u
          rw [localized_flatToSmallBall_eq n r d hr]
          exact (ContinuousLinearMap.le_opNorm _ u).trans
            (mul_le_mul_of_nonneg_right hC (norm_nonneg u))
        · intro I u hI hu
          rw [localized_flatToSmallBall_eq n r d hr]
          have hh : fixedSparseCoefficient*Real.sqrt d*(∑ i, |u i|) ≤
              spectralNuclearNorm (gaussianBilinearOperator n r d z u) := by
            apply le_of_not_gt
            intro hb
            exact hH ⟨I,u,hI,hu,hb⟩
          convert hh using 1 <;> simp only [fixedSparseCoefficient] <;> ring
  · exact Or.inl (Or.inl hC)

/-- Limit bookkeeping after the genuine uniform sparse estimate is available.
This deliberately named conditional helper is not the final endpoint. -/
theorem flat_mixed_limit_of_sparse_limit {α : ℝ}
    (hα : 0 < α) (hα' : α < 1/4) (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, (n d:ℝ) ≤ α*(d:ℝ)^2)
    (hSparse : Tendsto (fun d => (tensorGaussianLaw (n d) (2*(d/4))).real
      (flatSparseBad (n d) (2*(d/4)) d)) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun d => (tensorGaussianLaw (n d) (2*(d/4))).real
      (flatMixedBad (n d) (2*(d/4)) d numericalEta c)) atTop (𝓝 0) := by
  have hnNat : ∀ᶠ d in atTop, n d ≤ d^2 := by
    filter_upwards [hn] with d hd
    have hu : (n d:ℝ) ≤ (d:ℝ)^2 := hd.trans
      (mul_le_of_le_one_left (sq_nonneg _) (by linarith : α ≤ 1))
    exact_mod_cast hu
  obtain ⟨cS,hcS,_,hSmall⟩ := flat_small_probability_tendsto_zero hα hα'
    numerical_eta_range.1
  refine ⟨min cS ((1/2:ℝ)^39), numerical_final_constant_pos hcS, ?_⟩
  have hUpper := ((flat_continuity_probability_tendsto_zero n hnNat).add hSparse).add
    (hSmall n hn)
  simp only [zero_add] at hUpper
  apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _ hUpper
  filter_upwards [eventually_ge_atTop 4] with d hd
  calc
    _ ≤ (tensorGaussianLaw (n d) (2*(d/4))).real
        ((flatContinuity (n d) (2*(d/4)) d)ᶜ ∪ flatSparseBad (n d) (2*(d/4)) d ∪
          flatSmallBad (n d) (2*(d/4)) d numericalEta cS) :=
      measureReal_mono (flatMixedBad_subset (by omega) (by omega) (by omega))
    _ ≤ (tensorGaussianLaw (n d) (2*(d/4))).real
          ((flatContinuity (n d) (2*(d/4)) d)ᶜ ∪ flatSparseBad (n d) (2*(d/4)) d) +
        (tensorGaussianLaw (n d) (2*(d/4))).real
          (flatSmallBad (n d) (2*(d/4)) d numericalEta cS) := measureReal_union_le _ _
    _ ≤ _ := add_le_add_left (measureReal_union_le _ _) _

end GaussianEllipsoidStandalone
