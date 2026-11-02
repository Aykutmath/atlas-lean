import PaperPSDSphereWidth
import BMWidthAsymptotic
import BMFullEntryWidth
import BMGordonExpectations

noncomputable section
open MeasureTheory Filter Set GaussianEllipsoid GaussianTensorMoments GaussianMixedNormHelpers
open BMGeometry UCEscape
open scoped BigOperators InnerProductSpace Topology
namespace GaussianEllipsoid.PaperPSDSphereWidth

/-- Nonnegative mean of the sphere support; individual supports may be negative. -/
theorem sphereWidth_nonneg {d : ℕ} (hd : 0 < d) : 0 ≤ sphereWidth d := by
  have hi := sphereSupport_integrable hd
  have hp := gaussianProductLaw_neg_preserving (Fin d × Fin d)
  have hn : Integrable (fun x => sphereSupport d (-x)) (gaussianProductLaw (Fin d × Fin d)) :=
    (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  have he : (∫ x,sphereSupport d (-x) ∂gaussianProductLaw (Fin d × Fin d))=sphereWidth d :=
    BMGordon.integral_comp_preserving hp hi.aestronglyMeasurable
  have hs (x : (Fin d × Fin d) → ℝ) : 0 ≤ sphereSupport d x+sphereSupport d (-x) := by
    obtain ⟨S,hS⟩ := psdUnit_nonempty hd
    have hx : ⟪fullEntryMatrix x,S⟫_ℝ ≤ sphereSupport d x :=
      le_csSup (sphere_values_bddAbove d x) ⟨S,hS,rfl⟩
    have hy : ⟪fullEntryMatrix (-x),S⟫_ℝ ≤ sphereSupport d (-x) :=
      le_csSup (sphere_values_bddAbove d (-x)) ⟨S,hS,rfl⟩
    rw [fullEntry_neg,inner_neg_left] at hy
    linarith
  have h : 0 ≤ ∫ x, sphereSupport d x+sphereSupport d (-x)
      ∂gaussianProductLaw (Fin d × Fin d) := MeasureTheory.integral_nonneg hs
  rw [integral_add hi hn,he] at h
  change 0 ≤ sphereWidth d+sphereWidth d at h
  linarith

/-- Bounded-condition PSD unit matrices are a subset of the exact PSD unit sphere. -/
theorem conditionedWidth_le_sphereWidth {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) :
    conditionedWidth d κ ≤ sphereWidth d := by
  apply integral_mono (gaussianConditionedSupportRaw_integrable hd hκ) (sphereSupport_integrable hd)
  intro x
  rw [gaussianConditionedSupportRaw_eq_fullEntry]
  change conditionedSupport d κ (fullEntryMatrix x) ≤ sphereSupport d x
  apply csSup_le
  · obtain ⟨S,hS⟩ := conditionedUnit_nonempty hd hκ
    exact ⟨_,S,hS,rfl⟩
  · rintro y ⟨S,hS,rfl⟩
    apply le_csSup (sphere_values_bddAbove d x)
    refine ⟨operatorFrobenius S,?_,rfl⟩
    change IsPSD (frobeniusOperator (operatorFrobenius S)) ∧ _
    rw [frobeniusOperator_operatorFrobenius]
    exact ⟨hS.1.1,by simpa only [Metric.mem_sphere,dist_zero_right] using hS.2⟩

/-- Quantitative upper bound convenient for the normalized limit. -/
theorem normalizedSphereWidth_upper {d : ℕ} (hd : 0 < d) :
    sphereWidth d/(d:ℝ) ≤ (1+1/(d:ℝ))/2 := by
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hroot : Real.sqrt ((d:ℝ)*(d+1)/4) ≤ ((d:ℝ)+1)/2 := by
    apply Real.sqrt_le_left (by positivity) |>.mpr
    nlinarith
  have h := div_le_div_of_nonneg_right ((sphereWidth_le_sqrt hd).trans hroot) hdR.le
  calc
    sphereWidth d/(d:ℝ) ≤ (((d:ℝ)+1)/2)/(d:ℝ) := h
    _ = (1+1/(d:ℝ))/2 := by field_simp

/-- The lower bound uses the proved bounded-condition cone width, not an inference
from the sphere's upper bound. -/
theorem normalizedSphereWidth_tendsto :
    Tendsto (fun d : ℕ => sphereWidth d/(d:ℝ)) atTop (𝓝 (1/2:ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨κ,hκ,hlarge⟩ := exists_conditionNumber_eventually_width_lower (sub_pos.mpr ha)
    filter_upwards [hlarge,eventually_ge_atTop (1:ℕ)] with d hlow hd
    have hdpos : 0 < d := by omega
    have hdiv := div_le_div_of_nonneg_right (conditionedWidth_le_sphereWidth hdpos hκ)
      (Nat.cast_nonneg d)
    have hh : a < conditionedWidth d κ/(d:ℝ) := by linarith
    exact hh.trans_le hdiv
  · intro b hb
    have hi : Tendsto (fun d : ℕ => 1/(d:ℝ)) atTop (𝓝 (0:ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hu : Tendsto (fun d : ℕ => (1+1/(d:ℝ))/2) atTop (𝓝 (1/2:ℝ)) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).add hi).div_const 2
    filter_upwards [hu.eventually (Iio_mem_nhds hb),eventually_ge_atTop (1:ℕ)] with d hupper hd
    exact (normalizedSphereWidth_upper (by omega : 0 < d)).trans_lt hupper

/-- Exact asymptotic Gaussian width asserted in the paper overview. -/
theorem paper_normalized_sphere_width_sq_tendsto :
    Tendsto (fun d : ℕ => (paperGaussianSphereWidth d/(d:ℝ))^2) atTop (𝓝 (1/4:ℝ)) := by
  have h := normalizedSphereWidth_tendsto.pow 2
  simpa only [paperGaussianSphereWidth,paper_sphere_support_eq,sphereWidth,
    show (1/2:ℝ)^2=1/4 by norm_num] using h

#print axioms paper_normalized_sphere_width_sq_tendsto
end GaussianEllipsoid.PaperPSDSphereWidth
