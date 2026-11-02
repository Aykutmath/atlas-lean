import GaussianEllipsoid.DSABThread

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianEllipsoid

/-- Literal centered-L2 conclusion of paper Proposition4.1, for the same
arbitrary spectral-box minimizer used in the source. -/
theorem paper_huber_centered_l2
    (n : ℕ → ℕ) (α : ℝ) (hn : ∀ d, 0 < n d)
    (hconv : Tendsto (fun d => (n d:ℝ)/(d:ℝ)^2) atTop (𝓝 α))
    (hα : 0 < α) (hα4 : α < 1/4)
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hBM : BMminRisk n lo hi)
    (Sstar : ∀ d, Sample d (n d) → Square d)
    (hStar : ∀ d x, IsHuberMinimizer lo hi x (Sstar d x))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => (gaussianSampleLaw d (n d)).real
      {x | ε < euclidNorm (center (residual x (Sstar d x))) / (d:ℝ)}) atTop (𝓝 0) := by
  have h := huberResiduals_unconditional n α hn hconv hα hα4 lo hi hlo hle hBM
    Sstar hStar 1 (by norm_num) ε hε
  apply squeeze_zero (fun d => measureReal_nonneg) _ h
  intro d
  refine measureReal_mono ?_ (measure_lt_top _ _).ne
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  unfold dualMixed
  exact hx.trans_le (le_max_right _ _)

/-- The selector's Huber risk tends to zero from the literal approximate-risk
statement and the vanishing ridge error. No new selected minimizer is substituted. -/
theorem paper_huber_risk_tendsto
    (n : ℕ → ℕ) (hn : ∀ d, 0 < n d)
    (lo hi : ℝ) (hle : lo ≤ hi) (hBM : BMminRisk n lo hi)
    (Sstar : ∀ d, Sample d (n d) → Square d)
    (hStar : ∀ d x, IsHuberMinimizer lo hi x (Sstar d x))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => (gaussianSampleLaw d (n d)).real
      {x | ε < empiricalHuber (residual x (Sstar d x))}) atTop (𝓝 0) := by
  have hb := hBM 1 (by norm_num) (by norm_num) (ε/4) (by positivity)
  have hr := (fin_C_half_tendsto ((|lo|+|hi|+1)^2)).eventually
    (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))
  apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _ hb
  filter_upwards [hr] with d hd
  refine measureReal_mono ?_ (measure_lt_top _ _).ne
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  by_contra hnBM
  have hb0 : bmMinRisk d (n d) x lo hi 1 < ε/2 :=
    lt_of_le_of_lt (le_of_not_gt hnBM) (by linarith)
  have hsmall := selector_huber_of_bmMinRisk x (hn d) hle (hStar d x)
    (by norm_num : (1:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2) hb0
  linarith

/-- Deterministic mean control, with all normalization constants visible. -/
theorem paper_mean_sq_le_huber {n : ℕ} (hn : 0 < n) (r : Vector n)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hr : empiricalHuber r ≤ τ) :
    (mean r)^2 ≤ 12*τ := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hm := abs_mean_le_mean_abs hn r
  have ha := empirical_abs_le_of_huber_le hr
  have he : mean (fun i => |r i|) = empiricalAverage (fun i => |r i|) := by
    simp [mean, empiricalAverage, div_eq_mul_inv, mul_comm]
  rw [he] at hm
  have hmean : |mean r| ≤ Real.sqrt (2*τ)+2*τ := hm.trans ha
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hmean
  rw [sq_abs] at hsq
  have hsqrt := Real.sq_sqrt (show 0 ≤ 2*τ by positivity)
  have hcross := sq_nonneg (Real.sqrt (2*τ)-2*τ)
  have ht := mul_nonneg hτ (sub_nonneg.mpr hτ1)
  nlinarith

/-- Uncentered empirical energy decomposes exactly into centered energy and
the square of the mean. -/
theorem paper_energy_decomposition {n : ℕ} (hn : 0 < n) (r : Vector n) :
    (∑ i, (r i)^2)/(n:ℝ) = (euclidNorm (center r))^2/(n:ℝ)+(mean r)^2 := by
  have hid := squaredL2_center_identity hn r
  rw [euclidNorm_sq]
  unfold squaredL2 at hid
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp
  nlinarith [hid]

/-- Pathwise bridge from normalized centered-L2 and Huber bounds to raw energy. -/
theorem paper_energy_small {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (haspect : α/2*(d:ℝ)^2 ≤ n) (r : Vector n)
    (hl2 : euclidNorm (center r)/(d:ℝ) ≤ Real.sqrt (ε*α/8))
    (hh : empiricalHuber r ≤ min 1 (ε/48)) :
    (∑ i, (r i)^2)/(n:ℝ) ≤ ε := by
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnorm := (div_le_iff₀ hdR).mp hl2
  have hsq := (sq_le_sq₀ (euclidNorm_nonneg _) (by positivity)).mpr hnorm
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ ε*α/8)] at hsq
  have haspect' := mul_le_mul_of_nonneg_left haspect (show 0 ≤ ε/4 by positivity)
  have hcenter : (euclidNorm (center r))^2/(n:ℝ) ≤ ε/4 := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [hsq, haspect']
  have hmean := paper_mean_sq_le_huber hn r
    (show 0 ≤ min 1 (ε/48) by positivity) (min_le_left _ _) hh
  have hmean' : (mean r)^2 ≤ ε/4 := by
    have ht := min_le_right (1:ℝ) (ε/48)
    linarith
  rw [paper_energy_decomposition hn r]
  linarith

/-- Literal raw empirical-energy convergence in Proposition4.1. -/
theorem paper_huber_raw_energy
    (n : ℕ → ℕ) (α : ℝ) (hn : ∀ d, 0 < n d)
    (hconv : Tendsto (fun d => (n d:ℝ)/(d:ℝ)^2) atTop (𝓝 α))
    (hα : 0 < α) (hα4 : α < 1/4)
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hBM : BMminRisk n lo hi)
    (Sstar : ∀ d, Sample d (n d) → Square d)
    (hStar : ∀ d x, IsHuberMinimizer lo hi x (Sstar d x))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => (gaussianSampleLaw d (n d)).real
      {x | ε < (∑ i, (residual x (Sstar d x) i)^2)/(n d:ℝ)}) atTop (𝓝 0) := by
  have heps : 0 < Real.sqrt (ε*α/8) := Real.sqrt_pos.mpr (by positivity)
  have hsmall : 0 < min (1:ℝ) (ε/48) := by positivity
  have hL := paper_huber_centered_l2 n α hn hconv hα hα4 lo hi hlo hle hBM
    Sstar hStar _ heps
  have hH := paper_huber_risk_tendsto n hn lo hi hle hBM Sstar hStar _ hsmall
  have hsum := hL.add hH
  rw [zero_add] at hsum
  have haspect := hconv.eventually (lt_mem_nhds (show α/2 < α by linarith))
  apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _ hsum
  filter_upwards [haspect, eventually_ge_atTop 1] with d hdA hd
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hAn : α/2*(d:ℝ)^2 ≤ n d :=
    ((lt_div_iff₀ (sq_pos_of_pos hdR)).mp hdA).le
  have hsub : {x | ε < (∑ i, (residual x (Sstar d x) i)^2)/(n d:ℝ)} ⊆
      {x | Real.sqrt (ε*α/8) < euclidNorm (center (residual x (Sstar d x)))/(d:ℝ)} ∪
      {x | min 1 (ε/48) < empiricalHuber (residual x (Sstar d x))} := by
    intro x hx
    by_contra hnot
    have hnot' := not_or.mp hnot
    have he := paper_energy_small (by omega) (hn d) hα hε hAn
      (residual x (Sstar d x)) (le_of_not_gt hnot'.1) (le_of_not_gt hnot'.2)
    exact (not_lt_of_ge he) hx
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

end GaussianEllipsoid
#print axioms GaussianEllipsoid.paper_huber_centered_l2
#print axioms GaussianEllipsoid.paper_huber_raw_energy
