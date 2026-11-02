import AHHSphereSmoothApproximation
import AHHSphereMomentReduction
import AHHEntropyLimitClosure
import Mathlib.Analysis.SpecificLimits.Basic

/-! Honest final smooth-approximation reduction for the actual product sphere.
The smooth angular entropy estimate remains an explicit analytic premise. The
approximation sequence, its bounds, and both limiting integrals are proved. -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter
open AHHEntropyLimitClosure
open scoped ContDiff Topology
namespace AHHRadial

/-- Exact smooth-angular analytic premise, with no assumption about nonsmooth
observables or convergence of entropies. -/
def SmoothSpherePowerEntropyBound (n h : ℕ) : Prop :=
  ∀ g : SphereAmbient n h → ℝ, ContDiff ℝ ∞ g → LipschitzWith 1 g →
    (∀ z, 1 ≤ g z) → (∀ z, g z ≤ Real.sqrt n) → ∀ p : ℝ,
    entropy (directionsLaw n h)
        (fun d => (g (directionsToEuclidean n h d).val)^(2*p)) ≤
      p^2 / ((h : ℝ)-1) * (∫ d,
        ((g (directionsToEuclidean n h d).val)^2)^(p-1) ∂directionsLaw n h)

theorem continuous_directionsToEuclidean_val_approx (n h : ℕ) :
    Continuous (fun d : Directions n h => (directionsToEuclidean n h d).val) := by
  change Continuous (fun d : Directions n h =>
    WithLp.toLp 2 (fun j : Fin n × Bool =>
      if j.2 then ((d j.1).2 : CE h) else ((d j.1).1 : CE h)))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Bool => CE h)).comp
  apply continuous_pi
  intro j
  cases j.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- Uniform real-power bounds, including negative exponents, on `[1,b]`. -/
theorem rpow_bounds_of_one_le {x b : ℝ} (hx : 1 ≤ x) (hxb : x ≤ b) (q : ℝ) :
    Real.exp (- (|Real.log b| * |q|)) ≤ x^q ∧
      x^q ≤ Real.exp (|Real.log b| * |q|) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : |Real.log x| ≤ |Real.log b| := by
    rw [abs_of_nonneg hlognonneg]
    exact (Real.log_le_log hxpos hxb).trans (le_abs_self _)
  have hprod : |Real.log x * q| ≤ |Real.log b| * |q| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hlog (abs_nonneg _)
  rw [Real.rpow_def_of_pos hxpos]
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hprod).1,
    Real.exp_le_exp.mpr (abs_le.mp hprod).2⟩

theorem sq_rpow_eq_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) (q : ℝ) :
    (x^2)^q = x^(2*q) := by
  rw [Real.rpow_mul hx, Real.rpow_two]

theorem sqrt_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) (q : ℝ) :
    (Real.sqrt x)^(2*q) = x^q := by
  rw [← sq_rpow_eq_rpow_two_mul (Real.sqrt_nonneg x), Real.sq_sqrt hx]

/-- The genuine C∞ approximants converge uniformly, hence pointwise, to the
actual square-root covariance observable. The sharp Lipschitz bound is retained. -/
theorem exists_smooth_root_approximation_sequence (n h : ℕ) (hn : 0 < n) :
    ∃ g : ℕ → SphereAmbient n h → ℝ,
      (∀ k, ContDiff ℝ ∞ (g k)) ∧ (∀ k, LipschitzWith 1 (g k)) ∧
      (∀ k z, 1 ≤ g k z) ∧ (∀ k z, g k z ≤ Real.sqrt n) ∧
      (∀ k d, |g k (directionsToEuclidean n h d).val -
        Real.sqrt (unitCovarianceNorm n h d)| ≤ 1 / ((k : ℝ)+1)) ∧
      (∀ d, Tendsto (fun k => g k (directionsToEuclidean n h d).val) atTop
        (𝓝 (Real.sqrt (unitCovarianceNorm n h d)))) := by
  classical
  have he (k : ℕ) : 0 < 1 / ((k : ℝ)+1) := by positivity
  choose g hgc hgl hlo hhi heps hderiv using
    fun k => exists_smooth_root_approximation n h hn (he k)
  refine ⟨g, hgc, hgl, hlo, hhi, heps, ?_⟩
  intro d
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun k => dist_nonneg)
    (fun k => by simpa only [Real.dist_eq] using heps k d)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Applying the proved bounded entropy-limit theorem to the actual smooth
approximants closes the nonsmooth step, conditional only on the explicitly
stated smooth-angular entropy inequality. -/
theorem spherePowerEntropyBound_of_smooth (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h)
    (hSmooth : SmoothSpherePowerEntropyBound n h) : SpherePowerEntropyBound n h := by
  let := directionsLaw_probability n h (by omega)
  obtain ⟨g, hgc, hgl, hlo, hhi, heps, hlim⟩ :=
    exists_smooth_root_approximation_sequence n h hn
  let G : ℕ → Directions n h → ℝ := fun k d => g k (directionsToEuclidean n h d).val
  have hGm (k : ℕ) : Measurable (G k) :=
    ((hgc k).continuous.comp (continuous_directionsToEuclidean_val_approx n h)).measurable
  have hUpos (d : Directions n h) : 0 < unitCovarianceNorm n h d :=
    lt_of_lt_of_le zero_lt_one (one_le_unitCovarianceNorm n h hn d)
  have hrootpos (d : Directions n h) : 0 < Real.sqrt (unitCovarianceNorm n h d) :=
    Real.sqrt_pos.mpr (hUpos d)
  have hpowbound (q : ℝ) (k : ℕ) : ∀ᵐ d ∂directionsLaw n h,
      Real.exp (- (|Real.log (Real.sqrt n)| * |q|)) ≤ (G k d)^q ∧
      (G k d)^q ≤ Real.exp (|Real.log (Real.sqrt n)| * |q|) :=
    ae_of_all _ fun d => rpow_bounds_of_one_le
      (hlo k (directionsToEuclidean n h d).val)
      (hhi k (directionsToEuclidean n h d).val) q
  have hpowlim (q : ℝ) : ∀ᵐ d ∂directionsLaw n h,
      Tendsto (fun k => (G k d)^q) atTop
        (𝓝 ((Real.sqrt (unitCovarianceNorm n h d))^q)) :=
    ae_of_all _ fun d => (hlim d).rpow_const (Or.inl (hrootpos d).ne')
  have hIlim (q : ℝ) :
      Tendsto (fun k => ∫ d, (G k d)^q ∂directionsLaw n h) atTop
        (𝓝 (∫ d, (Real.sqrt (unitCovarianceNorm n h d))^q ∂directionsLaw n h)) :=
    tendsto_integral_of_uniform_bounds (directionsLaw n h)
      (fun k => (hGm k).pow_const q) (Real.exp_pos _)
      (hpowbound q) (hpowlim q)
  intro p
  have hE := entropy_le_of_approximation (directionsLaw n h)
    (fun k => (hGm k).pow_const (2*p)) (Real.exp_pos _)
    (hpowbound (2*p)) (hpowlim (2*p))
    (Ak := fun k => ∫ d, (G k d)^(2*(p-1)) ∂directionsLaw n h)
    (C := p^2 / ((h : ℝ)-1))
    (fun k => by
      have hs := hSmooth (g k) (hgc k) (hgl k) (hlo k) (hhi k) p
      convert hs using 1
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun d =>
        (sq_rpow_eq_rpow_two_mul
          (le_trans zero_le_one (hlo k (directionsToEuclidean n h d).val)) (p-1)).symm)
    (hIlim (2*(p-1)))
  have hrootpow (q : ℝ) :
      (fun d : Directions n h => (Real.sqrt (unitCovarianceNorm n h d))^(2*q)) =
      (fun d => (unitCovarianceNorm n h d)^q) := by
    funext d
    exact sqrt_rpow_two_mul (hUpos d).le q
  rw [hrootpow p, hrootpow (p-1),
    entropy_rpow_eq_powerEntropy (directionsLaw n h) _ hUpos p] at hE
  exact hE

#print axioms continuous_directionsToEuclidean_val_approx
#print axioms exists_smooth_root_approximation_sequence
#print axioms spherePowerEntropyBound_of_smooth
end AHHRadial
