import AHHBoundedPositiveMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Entropy is closed under uniformly positive, bounded almost-everywhere
limits on a probability space. Both integral limits are proved by dominated
convergence with explicit constant envelopes. No entropy convergence or
log-Sobolev inequality is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace AHHEntropyLimitClosure
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Entropy of a real-valued density. Positivity is imposed by the lemmas using it. -/
def entropy (Z : Ω → ℝ) : ℝ :=
  (∫ w, Z w * Real.log (Z w) ∂P) -
    (∫ w, Z w ∂P) * Real.log (∫ w, Z w ∂P)

omit [IsProbabilityMeasure P] in
/-- The limit inherits the same almost-everywhere bounds. -/
theorem ae_bounds_of_tendsto {Zk : ℕ → Ω → ℝ} {Z : Ω → ℝ} {a b : ℝ}
    (hbound : ∀ k, ∀ᵐ w ∂P, a ≤ Zk k w ∧ Zk k w ≤ b)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun k => Zk k w) atTop (𝓝 (Z w))) :
    ∀ᵐ w ∂P, a ≤ Z w ∧ Z w ≤ b := by
  have hb : ∀ᵐ w ∂P, ∀ k, a ≤ Zk k w ∧ Zk k w ≤ b := ae_all_iff.mpr hbound
  filter_upwards [hb, hlim] with w hw hl
  exact ⟨ge_of_tendsto' hl (fun k => (hw k).1),
    le_of_tendsto' hl (fun k => (hw k).2)⟩

theorem norm_le_of_bounds {a b x : ℝ} (ha : 0 < a) (hx : a ≤ x ∧ x ≤ b) :
    ‖x‖ ≤ |b| := by
  rw [Real.norm_eq_abs, abs_of_pos (ha.trans_le hx.1)]
  exact hx.2.trans (le_abs_self b)

/-- An explicit finite entropy-integrand envelope. -/
theorem norm_mul_log_le_of_bounds {a b x : ℝ} (ha : 0 < a)
    (hx : a ≤ x ∧ x ≤ b) :
    ‖x * Real.log x‖ ≤ |b| * (|Real.log a| + |Real.log b|) := by
  have hxpos := ha.trans_le hx.1
  have hloglow := Real.log_le_log ha hx.1
  have hlogup := Real.log_le_log hxpos hx.2
  have hlog : |Real.log x| ≤ |Real.log a| + |Real.log b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
    · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]
  rw [norm_mul, Real.norm_eq_abs (Real.log x)]
  exact mul_le_mul (norm_le_of_bounds ha hx) hlog (abs_nonneg _) (abs_nonneg _)

theorem integrable_of_uniform_bounds {Z : Ω → ℝ} {a b : ℝ}
    (hZ : Measurable Z) (ha : 0 < a)
    (hbound : ∀ᵐ w ∂P, a ≤ Z w ∧ Z w ≤ b) : Integrable Z P := by
  apply (integrable_const (|b| : ℝ)).mono' hZ.aestronglyMeasurable
  filter_upwards [hbound] with w hw
  exact norm_le_of_bounds ha hw

theorem integrable_mul_log_of_uniform_bounds {Z : Ω → ℝ} {a b : ℝ}
    (hZ : Measurable Z) (ha : 0 < a)
    (hbound : ∀ᵐ w ∂P, a ≤ Z w ∧ Z w ≤ b) :
    Integrable (fun w => Z w * Real.log (Z w)) P := by
  apply (integrable_const (|b| * (|Real.log a| + |Real.log b|))).mono'
    (hZ.mul hZ.log).aestronglyMeasurable
  filter_upwards [hbound] with w hw
  exact norm_mul_log_le_of_bounds ha hw

/-- The first integral converges with the explicit envelope `|b|`. -/
theorem tendsto_integral_of_uniform_bounds {Zk : ℕ → Ω → ℝ} {Z : Ω → ℝ} {a b : ℝ}
    (hZk : ∀ k, Measurable (Zk k)) (ha : 0 < a)
    (hbound : ∀ k, ∀ᵐ w ∂P, a ≤ Zk k w ∧ Zk k w ≤ b)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun k => Zk k w) atTop (𝓝 (Z w))) :
    Tendsto (fun k => ∫ w, Zk k w ∂P) atTop (𝓝 (∫ w, Z w ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => |b|)
    (fun k => (hZk k).aestronglyMeasurable) (integrable_const _) _ hlim
  intro k
  filter_upwards [hbound k] with w hw
  exact norm_le_of_bounds ha hw

/-- The logarithmic integral converges under an explicit finite constant envelope. -/
theorem tendsto_integral_mul_log_of_uniform_bounds
    {Zk : ℕ → Ω → ℝ} {Z : Ω → ℝ} {a b : ℝ}
    (hZk : ∀ k, Measurable (Zk k)) (ha : 0 < a)
    (hbound : ∀ k, ∀ᵐ w ∂P, a ≤ Zk k w ∧ Zk k w ≤ b)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun k => Zk k w) atTop (𝓝 (Z w))) :
    Tendsto (fun k => ∫ w, Zk k w * Real.log (Zk k w) ∂P) atTop
      (𝓝 (∫ w, Z w * Real.log (Z w) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => |b| * (|Real.log a| + |Real.log b|))
    (fun k => ((hZk k).mul (hZk k).log).aestronglyMeasurable) (integrable_const _)
  · intro k
    filter_upwards [hbound k] with w hw
    exact norm_mul_log_le_of_bounds ha hw
  · filter_upwards [hlim, ae_bounds_of_tendsto P hbound hlim] with w hw hb
    exact hw.mul ((Real.continuousAt_log (ha.trans_le hb.1).ne').tendsto.comp hw)

/-- Entropy convergence is proved, not assumed. Measurability and bounds of the
limit are not extra hypotheses: dominated convergence and closed order suffice. -/
theorem tendsto_entropy_of_uniform_bounds {Zk : ℕ → Ω → ℝ} {Z : Ω → ℝ} {a b : ℝ}
    (hZk : ∀ k, Measurable (Zk k)) (ha : 0 < a)
    (hbound : ∀ k, ∀ᵐ w ∂P, a ≤ Zk k w ∧ Zk k w ≤ b)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun k => Zk k w) atTop (𝓝 (Z w))) :
    Tendsto (fun k => entropy P (Zk k)) atTop (𝓝 (entropy P Z)) := by
  have hmean := tendsto_integral_of_uniform_bounds P hZk ha hbound hlim
  have hmean_low (k : ℕ) : a ≤ ∫ w, Zk k w ∂P := by
    have h := integral_mono_ae (integrable_const a)
      (integrable_of_uniform_bounds P (hZk k) ha (hbound k))
      ((hbound k).mono (fun _ hw => hw.1))
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hmean_pos : 0 < ∫ w, Z w ∂P :=
    ha.trans_le (ge_of_tendsto' hmean hmean_low)
  exact (tendsto_integral_mul_log_of_uniform_bounds P hZk ha hbound hlim).sub
    (hmean.mul ((Real.continuousAt_log hmean_pos.ne').tendsto.comp hmean))

/-- Inequalities pass to the limit once both sides have their genuine limits. -/
theorem entropy_le_of_approximation {Zk : ℕ → Ω → ℝ} {Z : Ω → ℝ} {a b C A : ℝ}
    {Ak : ℕ → ℝ} (hZk : ∀ k, Measurable (Zk k)) (ha : 0 < a)
    (hbound : ∀ k, ∀ᵐ w ∂P, a ≤ Zk k w ∧ Zk k w ≤ b)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun k => Zk k w) atTop (𝓝 (Z w)))
    (hineq : ∀ k, entropy P (Zk k) ≤ C * Ak k)
    (hA : Tendsto Ak atTop (𝓝 A)) : entropy P Z ≤ C * A := by
  exact le_of_tendsto_of_tendsto'
    (tendsto_entropy_of_uniform_bounds P hZk ha hbound hlim)
    (tendsto_const_nhds.mul hA) hineq

/-- Convenient square-test version for Gaussian and sphere approximation arguments. -/
theorem tendsto_entropy_sq_of_uniform_bounds {Hk : ℕ → Ω → ℝ} {H : Ω → ℝ} {a b : ℝ}
    (hHk : ∀ k, Measurable (Hk k)) (ha : 0 < a)
    (hbound : ∀ k, ∀ᵐ w ∂P, a ≤ Hk k w ∧ Hk k w ≤ b)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun k => Hk k w) atTop (𝓝 (H w))) :
    Tendsto (fun k => entropy P (fun w => (Hk k w)^2)) atTop
      (𝓝 (entropy P (fun w => (H w)^2))) := by
  apply tendsto_entropy_of_uniform_bounds P (fun k => (hHk k).pow_const 2)
    (sq_pos_of_pos ha) (b := b^2)
  · intro k
    filter_upwards [hbound k] with w hw
    have hz : 0 ≤ Hk k w := ha.le.trans hw.1
    constructor
    · exact pow_le_pow_left₀ ha.le hw.1 2
    · exact pow_le_pow_left₀ hz hw.2 2
  · exact hlim.mono fun _ hw => hw.pow 2

theorem entropy_sq_le_of_approximation {Hk : ℕ → Ω → ℝ} {H : Ω → ℝ}
    {a b C A : ℝ} {Ak : ℕ → ℝ}
    (hHk : ∀ k, Measurable (Hk k)) (ha : 0 < a)
    (hbound : ∀ k, ∀ᵐ w ∂P, a ≤ Hk k w ∧ Hk k w ≤ b)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun k => Hk k w) atTop (𝓝 (H w)))
    (hineq : ∀ k, entropy P (fun w => (Hk k w)^2) ≤ C * Ak k)
    (hA : Tendsto Ak atTop (𝓝 A)) :
    entropy P (fun w => (H w)^2) ≤ C * A := by
  exact le_of_tendsto_of_tendsto'
    (tendsto_entropy_sq_of_uniform_bounds P hHk ha hbound hlim)
    (tendsto_const_nhds.mul hA) hineq

omit [IsProbabilityMeasure P] in
/-- The entropy functional matches the existing exponential-power convention. -/
theorem entropy_exp_eq_powerEntropy (X : Ω → ℝ) (p : ℝ) :
    entropy P (fun w => Real.exp (p * X w)) =
      AHHBoundedPositiveMoments.powerEntropy P X p := by
  unfold entropy AHHBoundedPositiveMoments.powerEntropy mgf
  have heq : (fun w => Real.exp (p * X w) * Real.log (Real.exp (p * X w))) =
      (fun w => p * (X w * Real.exp (p * X w))) := by
    funext w
    rw [Real.log_exp]
    ring
  rw [heq, integral_const_mul]

/-- Pointwise bounds can be supplied without constructing almost-everywhere events. -/
theorem tendsto_entropy_of_bounds {Zk : ℕ → Ω → ℝ} {Z : Ω → ℝ} {a b : ℝ}
    (hZk : ∀ k, Measurable (Zk k)) (ha : 0 < a)
    (hbound : ∀ k w, a ≤ Zk k w ∧ Zk k w ≤ b)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun k => Zk k w) atTop (𝓝 (Z w))) :
    Tendsto (fun k => entropy P (Zk k)) atTop (𝓝 (entropy P Z)) :=
  tendsto_entropy_of_uniform_bounds P hZk ha (fun k => ae_of_all P (hbound k)) hlim

omit [IsProbabilityMeasure P] in
/-- Entropy is unchanged by almost-everywhere equality. -/
theorem entropy_congr_ae {Z W : Ω → ℝ} (h : Z =ᵐ[P] W) :
    entropy P Z = entropy P W := by
  unfold entropy
  rw [integral_congr_ae h]
  congr 1
  apply integral_congr_ae
  exact h.mono fun _ hw => by dsimp only; rw [hw]

omit [IsProbabilityMeasure P] in
/-- Real powers of a positive observable match the existing power entropy. -/
theorem entropy_rpow_eq_powerEntropy (U : Ω → ℝ) (hU : ∀ w, 0 < U w) (p : ℝ) :
    entropy P (fun w => (U w)^p) =
      AHHBoundedPositiveMoments.powerEntropy P (fun w => Real.log (U w)) p := by
  have heq : (fun w => (U w)^p) = (fun w => Real.exp (p * Real.log (U w))) := by
    funext w
    rw [Real.rpow_def_of_pos (hU w), mul_comm]
  rw [heq, entropy_exp_eq_powerEntropy]

omit [IsProbabilityMeasure P] in
/-- The square of the half power gives precisely the entropy of the full power. -/
theorem entropy_rpow_half_sq_eq_powerEntropy (U : Ω → ℝ)
    (hU : ∀ w, 0 < U w) (p : ℝ) :
    entropy P (fun w => ((U w)^(p/2))^2) =
      AHHBoundedPositiveMoments.powerEntropy P (fun w => Real.log (U w)) p := by
  have heq : (fun w => ((U w)^(p/2))^2) = (fun w => (U w)^p) := by
    funext w
    rw [← Real.rpow_mul_natCast (hU w).le]
    congr 1
    norm_num
  rw [heq, entropy_rpow_eq_powerEntropy P U hU p]

#print axioms tendsto_entropy_of_uniform_bounds
#print axioms entropy_le_of_approximation
#print axioms tendsto_entropy_sq_of_uniform_bounds
#print axioms entropy_sq_le_of_approximation
#print axioms entropy_exp_eq_powerEntropy
#print axioms entropy_congr_ae
#print axioms entropy_rpow_eq_powerEntropy
#print axioms entropy_rpow_half_sq_eq_powerEntropy
end AHHEntropyLimitClosure
