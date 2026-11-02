import AHHSphereEuclideanGeometry
import AHHBlockNormalizationEnergy
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Continuous angular power weights on the actual compact product of spheres. -/
noncomputable section
open MeasureTheory Set GaussianMixedNormHelpers
open scoped BigOperators ContDiff
namespace AHHRadial

/-- The coordinate-faithful embedding of all sphere directions is continuous. -/
theorem continuous_directionsToEuclidean_val (n h : ℕ) :
    Continuous (fun d : Directions n h => (directionsToEuclidean n h d).val) := by
  unfold directionsToEuclidean
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Bool => CE h)).comp
  apply continuous_pi
  rintro ⟨i, b⟩
  cases b
  · exact continuous_subtype_val.comp (continuous_fst.comp (continuous_apply i))
  · exact continuous_subtype_val.comp (continuous_snd.comp (continuous_apply i))

/-- One block of the exact angular energy, including the real power chain-rule factor. -/
def angularPowerWeight (n h : ℕ) (g : SphereAmbient n h → ℝ) (p : ℝ)
    (j : Fin n × Bool) (d : Directions n h) : ℝ :=
  p ^ 2 * ((g (directionsToEuclidean n h d).val) ^ 2) ^ (p - 1) *
    ‖blockPartial (fderiv ℝ g (directionsToEuclidean n h d).val) j‖ ^ 2

theorem angularPowerWeight_nonneg (n h : ℕ) (g : SphereAmbient n h → ℝ) (p : ℝ)
    (j : Fin n × Bool) (d : Directions n h) :
    0 ≤ angularPowerWeight n h g p j d := by
  unfold angularPowerWeight
  positivity

/-- A positive continuous ambient function has continuous angular real powers, at every exponent. -/
theorem continuous_angular_rpow (n h : ℕ) (g : SphereAmbient n h → ℝ)
    (hg : Continuous g) (hpos : ∀ z, 1 ≤ g z) (q : ℝ) :
    Continuous (fun d : Directions n h => (g (directionsToEuclidean n h d).val) ^ q) := by
  apply (hg.comp (continuous_directionsToEuclidean_val n h)).rpow_const
  intro d
  exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (hpos _)))

/-- The square uses a natural exponent; the outer exponent is a real power. -/
theorem continuous_angular_sq_rpow (n h : ℕ) (g : SphereAmbient n h → ℝ)
    (hg : Continuous g) (hpos : ∀ z, 1 ≤ g z) (q : ℝ) :
    Continuous (fun d : Directions n h => ((g (directionsToEuclidean n h d).val) ^ 2) ^ q) := by
  apply ((hg.comp (continuous_directionsToEuclidean_val n h)).pow 2).rpow_const
  intro d
  apply Or.inl
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one (hpos _)))

theorem continuous_angularPowerWeight (n h : ℕ) (g : SphereAmbient n h → ℝ)
    (hg : ContDiff ℝ ∞ g) (hpos : ∀ z, 1 ≤ g z) (p : ℝ) (j : Fin n × Bool) :
    Continuous (angularPowerWeight n h g p j) := by
  have hd : Continuous (fun d : Directions n h =>
      blockPartial (fderiv ℝ g (directionsToEuclidean n h d).val) j) := by
    exact ((hg.continuous_fderiv (by simp)).comp
      (continuous_directionsToEuclidean_val n h)).clm_comp_const (blockInclude j)
  exact (continuous_const.mul (continuous_angular_sq_rpow n h g hg.continuous hpos (p - 1))).mul
    (hd.norm.pow 2)

theorem measurable_angularPowerWeight (n h : ℕ) (g : SphereAmbient n h → ℝ)
    (hg : ContDiff ℝ ∞ g) (hpos : ∀ z, 1 ≤ g z) (p : ℝ) (j : Fin n × Bool) :
    Measurable (angularPowerWeight n h g p j) :=
  (continuous_angularPowerWeight n h g hg hpos p j).measurable

/-- Every continuous scalar angular function is integrable for the actual product-sphere law. -/
theorem integrable_continuous_directions (n h : ℕ) (hh : 0 < h)
    (f : Directions n h → ℝ) (hf : Continuous f) : Integrable f (directionsLaw n h) := by
  let : NeZero h := ⟨Nat.ne_of_gt hh⟩
  let := directionsLaw_probability n h hh
  let : CompactSpace (UnitDirection h) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : CE h) 1)
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hf.continuousOn.integrableOn_compact (μ := directionsLaw n h) isCompact_univ

theorem integrable_angularPowerWeight (n h : ℕ) (hh : 0 < h)
    (g : SphereAmbient n h → ℝ) (hg : ContDiff ℝ ∞ g) (hpos : ∀ z, 1 ≤ g z)
    (p : ℝ) (j : Fin n × Bool) :
    Integrable (angularPowerWeight n h g p j) (directionsLaw n h) :=
  integrable_continuous_directions n h hh _ (continuous_angularPowerWeight n h g hg hpos p j)

theorem integrable_angular_rpow (n h : ℕ) (hh : 0 < h)
    (g : SphereAmbient n h → ℝ) (hg : Continuous g) (hpos : ∀ z, 1 ≤ g z) (q : ℝ) :
    Integrable (fun d : Directions n h => (g (directionsToEuclidean n h d).val) ^ q)
      (directionsLaw n h) :=
  integrable_continuous_directions n h hh _ (continuous_angular_rpow n h g hg hpos q)

theorem integrable_angular_sq_rpow (n h : ℕ) (hh : 0 < h)
    (g : SphereAmbient n h → ℝ) (hg : Continuous g) (hpos : ∀ z, 1 ≤ g z) (q : ℝ) :
    Integrable (fun d : Directions n h => ((g (directionsToEuclidean n h d).val) ^ 2) ^ q)
      (directionsLaw n h) :=
  integrable_continuous_directions n h hh _ (continuous_angular_sq_rpow n h g hg hpos q)

/-- The block sum costs no dimension factor. -/
theorem sum_angularPowerWeight_le (n h : ℕ) (g : SphereAmbient n h → ℝ)
    (hg : LipschitzWith 1 g) (p : ℝ) (d : Directions n h) :
    ∑ j, angularPowerWeight n h g p j d ≤
      p ^ 2 * ((g (directionsToEuclidean n h d).val) ^ 2) ^ (p - 1) :=
  sum_powered_blockPartial_sq_le g hg _ p

/-- The sum of the integrated angular block weights keeps the sharp total-energy constant. -/
theorem sum_integral_angularPowerWeight_le (n h : ℕ) (hh : 0 < h)
    (g : SphereAmbient n h → ℝ) (hg : ContDiff ℝ ∞ g) (hpos : ∀ z, 1 ≤ g z)
    (hLip : LipschitzWith 1 g) (p : ℝ) :
    ∑ j, ∫ d, angularPowerWeight n h g p j d ∂directionsLaw n h ≤
      p ^ 2 * ∫ d, ((g (directionsToEuclidean n h d).val) ^ 2) ^ (p - 1)
        ∂directionsLaw n h := by
  rw [← integral_finsetSum _ (fun j _ => integrable_angularPowerWeight n h hh g hg hpos p j),
    ← integral_const_mul]
  apply integral_mono
  · exact integrable_finsetSum _ (fun j _ => integrable_angularPowerWeight n h hh g hg hpos p j)
  · exact (integrable_angular_sq_rpow n h hh g hg.continuous hpos (p - 1)).const_mul (p ^ 2)
  · exact sum_angularPowerWeight_le n h g hLip p

#print axioms continuous_directionsToEuclidean_val
#print axioms continuous_angular_rpow
#print axioms continuous_angular_sq_rpow
#print axioms integrable_continuous_directions
#print axioms angularPowerWeight_nonneg
#print axioms continuous_angularPowerWeight
#print axioms measurable_angularPowerWeight
#print axioms integrable_angularPowerWeight
#print axioms integrable_angular_rpow
#print axioms integrable_angular_sq_rpow
#print axioms sum_angularPowerWeight_le
#print axioms sum_integral_angularPowerWeight_le
end AHHRadial
