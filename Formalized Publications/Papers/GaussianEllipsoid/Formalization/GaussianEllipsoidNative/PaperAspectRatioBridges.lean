import StrictThresholdProjectFinal
import AspectRatioLimit

noncomputable section
open Filter
open scoped ENNReal Topology
namespace GaussianEllipsoid

/-- Away from dimension zero, the extended ratio is exactly the embedding of
the ordinary nonnegative real ratio. -/
theorem dimensionRatio_eq_ofReal_real_ratio (n : ℕ → ℕ) {d : ℕ} (hd : 0 < d) :
    dimensionRatio n d = ENNReal.ofReal ((n d : ℝ)/(d : ℝ)^2) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < (d:ℝ)^2),
    ENNReal.ofReal_pow (Nat.cast_nonneg d), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]
  rfl

/-- The usual strict upper-limit condition is equivalent to an eventual
finite real gap below one quarter. No convergence or positive lower ratio
is assumed, and no conditionally-complete `Real.limsup` convention is used. -/
theorem below_ratio_iff_eventual_real_gap (n : ℕ → ℕ) :
    limsup (dimensionRatio n) atTop < (1/4 : ℝ≥0∞) ↔
      ∃ a : ℝ, 0 < a ∧ a < 1/4 ∧
        ∀ᶠ d in atTop, (n d : ℝ)/(d : ℝ)^2 ≤ a := by
  constructor
  · intro h
    obtain ⟨a,ha,ha4,hev⟩ :=
      GaussianEllipsoidFinalPassage.exists_eventual_real_aspect_gap (dimensionRatio n) h
    refine ⟨a,ha,ha4,?_⟩
    filter_upwards [hev,eventually_ge_atTop 1] with d hda hd
    exact ((dimensionRatio_lt_ofReal hd ha).mp hda).le
  · rintro ⟨a,ha,ha4,hev⟩
    have hle : limsup (dimensionRatio n) atTop ≤ ENNReal.ofReal a := by
      apply limsup_le_of_le (by isBoundedDefault)
      filter_upwards [hev,eventually_ge_atTop 1] with d hda hd
      rw [dimensionRatio_eq_ofReal_real_ratio n (by omega)]
      exact ENNReal.ofReal_le_ofReal hda
    apply hle.trans_lt
    rw [ennreal_quarter_eq_ofReal]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mpr ha4

/-- The usual strict lower-limit condition is equivalent to an eventual
finite real gap above one quarter, including unbounded ratios and infinite
lower limit. No global upper bound on the sample-count sequence is inserted. -/
theorem above_ratio_iff_eventual_real_gap (n : ℕ → ℕ) :
    (1/4 : ℝ≥0∞) < liminf (dimensionRatio n) atTop ↔
      ∃ a : ℝ, 1/4 < a ∧ ∀ᶠ d in atTop, a ≤ (n d : ℝ)/(d : ℝ)^2 := by
  constructor
  · intro h
    obtain ⟨am,a,ham,hama,ha⟩ := exists_aspect_pair h
    have hapos : 0 < a := by linarith
    refine ⟨a,by linarith,?_⟩
    have hev := eventually_lt_of_lt_liminf ha
    filter_upwards [hev,eventually_ge_atTop 1] with d hda hd
    exact ((dimensionRatio_gt_ofReal hd hapos).mp hda).le
  · rintro ⟨a,ha,hev⟩
    have hle : ENNReal.ofReal a ≤ liminf (dimensionRatio n) atTop := by
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [hev,eventually_ge_atTop 1] with d hda hd
      rw [dimensionRatio_eq_ofReal_real_ratio n (by omega)]
      exact ENNReal.ofReal_le_ofReal hda
    apply lt_of_lt_of_le ?_ hle
    rw [ennreal_quarter_eq_ofReal]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)).mpr ha

/-- Main below-threshold result in the exact eventual-real-gap formulation. -/
theorem strictFitProbability_tendsto_one_of_eventual_real_gap (n : ℕ → ℕ)
    (hn : ∀ d, 0 < n d)
    (hgap : ∃ a : ℝ, 0 < a ∧ a < 1/4 ∧
      ∀ᶠ d in atTop, (n d : ℝ)/(d : ℝ)^2 ≤ a) :
    Tendsto (fun d => strictFitProbability d (n d)) atTop (nhds 1) :=
  strict_threshold_unconditional.1 n hn ((below_ratio_iff_eventual_real_gap n).mpr hgap)

/-- Main above-threshold result, also for arbitrarily unbounded sample ratios. -/
theorem fitProbability_tendsto_zero_of_eventual_real_gap (n : ℕ → ℕ)
    (hn : ∀ d, 0 < n d)
    (hgap : ∃ a : ℝ, 1/4 < a ∧
      ∀ᶠ d in atTop, a ≤ (n d : ℝ)/(d : ℝ)^2) :
    Tendsto (fun d => fitProbability d (n d)) atTop (nhds 0) :=
  strict_threshold_unconditional.2 n hn ((above_ratio_iff_eventual_real_gap n).mpr hgap)

#print axioms below_ratio_iff_eventual_real_gap
#print axioms above_ratio_iff_eventual_real_gap
#print axioms strictFitProbability_tendsto_one_of_eventual_real_gap
#print axioms fitProbability_tendsto_zero_of_eventual_real_gap
end GaussianEllipsoid
