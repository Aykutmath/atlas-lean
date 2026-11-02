import AHHBlockNormalizationEnergy
import AHHSphereAmbientGaussianLaw
import AHHAngularGaussianIntegrability
import AHHAngularPowerWeights
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Sharp integrated energy of smooth angular approximants under the actual Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers
open scoped BigOperators ContDiff
namespace AHHRadial

/-- Block normalization agrees coordinate by coordinate with the genuine extracted directions. -/
theorem blockNormalize_pairsToSphereAmbient (n h : ℕ) [NeZero h]
    (z : Fin n → CE h × CE h) (hz : ∀ i, (z i).1 ≠ 0 ∧ (z i).2 ≠ 0) :
    blockNormalize (pairsToSphereAmbient n h z) =
      (directionsToEuclidean n h (gaussianDirections n h z)).val := by
  ext ⟨i,b⟩ : 1
  cases b
  · change radialNormalize (z i).1 = (direction (z i).1).val
    simp [direction, (hz i).1, radialNormalize]
  · change radialNormalize (z i).2 = (direction (z i).2).val
    simp [direction, (hz i).2, radialNormalize]

/-- Positive reconstructed radii normalize back to exactly the original directions. -/
theorem blockNormalize_assembleSample (n h : ℕ) [NeZero h]
    (w : (Fin n → Radius × Radius) × Directions n h) :
    blockNormalize (pairsToSphereAmbient n h (assembleSample n h w)) =
      (directionsToEuclidean n h w.2).val := by
  rw [blockNormalize_pairsToSphereAmbient, gaussianDirections_assembleSample]
  intro i
  constructor
  · intro he
    have hn := norm_assemble ((w.2 i).1, (w.1 i).1)
    change ‖(assembleSample n h w i).1‖ = _ at hn
    rw [he, norm_zero] at hn
    exact (w.1 i).1.property.ne' hn.symm
  · intro he
    have hn := norm_assemble ((w.2 i).2, (w.1 i).2)
    change ‖(assembleSample n h w i).2‖ = _ at hn
    rw [he, norm_zero] at hn
    exact (w.1 i).2.property.ne' hn.symm

/-- Almost-everywhere sharp derivative domination by the literal independent angular weights. -/
theorem ae_powered_angular_energy_le (n h : ℕ) [NeZero h] (hh : 0 < h)
    (g : SphereAmbient n h → ℝ) (hg : ContDiff ℝ ∞ g) (hpos : ∀ z, 1 ≤ g z) (p : ℝ) :
    ∀ᵐ z ∂gaussianPairsLaw n h,
      ‖fderiv ℝ (fun y => g (blockNormalize y) ^ p) (pairsToSphereAmbient n h z)‖ ^ 2 ≤
        ∑ j : Fin n × Bool, angularPowerWeight n h g p j (gaussianDirections n h z) /
          ‖if j.2 then (z j.1).2 else (z j.1).1‖ ^ 2 := by
  filter_upwards [gaussianPairs_ae_nonzero n h hh] with z hz
  have hz' : ∀ j, (pairsToSphereAmbient n h z) j ≠ 0 := by
    rintro ⟨i,b⟩
    cases b
    · exact (hz i).1
    · exact (hz i).2
  have hb := norm_sq_fderiv_rpow_comp_blockNormalize_le g (pairsToSphereAmbient n h z) p
    (hg.differentiable (by simp)).differentiableAt
    (by linarith [hpos (blockNormalize (pairsToSphereAmbient n h z))]) hz'
  rw [blockNormalize_pairsToSphereAmbient n h z hz] at hb
  exact hb

/-- The sum of angular weights divided by squared radii is integrable. -/
theorem powered_angular_upper_integrable (n h : ℕ) [NeZero h] (hh : 2 ≤ h)
    (g : SphereAmbient n h → ℝ) (hg : ContDiff ℝ ∞ g) (hpos : ∀ z, 1 ≤ g z) (p : ℝ) :
    Integrable (fun z : Fin n → CE h × CE h =>
      ∑ j : Fin n × Bool, angularPowerWeight n h g p j (gaussianDirections n h z) /
        ‖if j.2 then (z j.1).2 else (z j.1).1‖ ^ 2) (gaussianPairsLaw n h) := by
  apply integrable_finsetSum
  intro j _
  exact gaussian_angular_weight_div_norm_sq_integrable n h hh j.1 j.2 _
    (integrable_angularPowerWeight n h (by omega) g hg hpos p j)

theorem integral_powered_angular_upper_le (n h : ℕ) [NeZero h] (hh : 2 ≤ h)
    (g : SphereAmbient n h → ℝ) (hg : ContDiff ℝ ∞ g) (hpos : ∀ z, 1 ≤ g z)
    (hLip : LipschitzWith 1 g) (p : ℝ) :
    (∫ z : Fin n → CE h × CE h,
      ∑ j : Fin n × Bool, angularPowerWeight n h g p j (gaussianDirections n h z) /
        ‖if j.2 then (z j.1).2 else (z j.1).1‖ ^ 2 ∂gaussianPairsLaw n h) ≤
      (h : ℝ) / ((h : ℝ) - 1) * p ^ 2 *
        (∫ d, ((g (directionsToEuclidean n h d).val) ^ 2) ^ (p - 1) ∂directionsLaw n h) := by
  rw [integral_finsetSum _ (fun j _ =>
    gaussian_angular_weight_div_norm_sq_integrable n h hh j.1 j.2 _
      (integrable_angularPowerWeight n h (by omega) g hg hpos p j))]
  simp_rw [gaussian_angular_weight_div_norm_sq n h hh _ _ _
    (measurable_angularPowerWeight n h g hg hpos p _)]
  rw [← Finset.mul_sum, mul_assoc]
  apply mul_le_mul_of_nonneg_left (sum_integral_angularPowerWeight_le n h (by omega)
    g hg hpos hLip p)
  have hh1 : (1 : ℝ) < h := by exact_mod_cast (show 1 < h by omega)
  positivity

/-- The actual powered normalized pullback has integrable derivative energy. -/
theorem integrable_powered_angular_energy (n h : ℕ) [NeZero h] (hh : 2 ≤ h)
    (g : SphereAmbient n h → ℝ) (hg : ContDiff ℝ ∞ g) (hpos : ∀ z, 1 ≤ g z) (p : ℝ) :
    Integrable (fun z : SphereAmbient n h =>
      ‖fderiv ℝ (fun y => g (blockNormalize y) ^ p) z‖ ^ 2) (sphereAmbientGaussianLaw n h) := by
  have hm : Measurable (fun z : SphereAmbient n h =>
      ‖fderiv ℝ (fun y => g (blockNormalize y) ^ p) z‖ ^ 2) :=
    (measurable_fderiv ℝ _).norm.pow_const 2
  apply ((pairsToSphereAmbient_preserving n h).integrable_comp hm.aestronglyMeasurable).mp
  exact (powered_angular_upper_integrable n h hh g hg hpos p).mono_nonneg
    ((hm.comp (pairsToSphereAmbient_preserving n h).measurable).aestronglyMeasurable)
    (ae_of_all _ fun z => sq_nonneg _)
    (ae_powered_angular_energy_le n h (by omega) g hg hpos p)

/-- Integrated sharp angular energy for the actual independent Gaussian ensemble. -/
theorem integral_powered_angular_energy_le (n h : ℕ) [NeZero h] (hh : 2 ≤ h)
    (g : SphereAmbient n h → ℝ) (hg : ContDiff ℝ ∞ g) (hpos : ∀ z, 1 ≤ g z)
    (hLip : LipschitzWith 1 g) (p : ℝ) :
    (∫ z : SphereAmbient n h,
      ‖fderiv ℝ (fun y => g (blockNormalize y) ^ p) z‖ ^ 2 ∂sphereAmbientGaussianLaw n h) ≤
      (h : ℝ) / ((h : ℝ) - 1) * p ^ 2 *
        (∫ d, ((g (directionsToEuclidean n h d).val) ^ 2) ^ (p - 1) ∂directionsLaw n h) := by
  have hm : Measurable (fun z : SphereAmbient n h =>
      ‖fderiv ℝ (fun y => g (blockNormalize y) ^ p) z‖ ^ 2) :=
    (measurable_fderiv ℝ _).norm.pow_const 2
  rw [sphereAmbientGaussianLaw, integral_map
    (pairsToSphereAmbient_preserving n h).measurable.aemeasurable hm.aestronglyMeasurable]
  apply (integral_mono_ae ?_ (powered_angular_upper_integrable n h hh g hg hpos p)
    (ae_powered_angular_energy_le n h (by omega) g hg hpos p)).trans
    (integral_powered_angular_upper_le n h hh g hg hpos hLip p)
  exact (pairsToSphereAmbient_preserving n h).integrable_comp_of_integrable
    (integrable_powered_angular_energy n h hh g hg hpos p)

#print axioms blockNormalize_pairsToSphereAmbient
#print axioms blockNormalize_assembleSample
#print axioms ae_powered_angular_energy_le
#print axioms integrable_powered_angular_energy
#print axioms integral_powered_angular_energy_le
end AHHRadial
