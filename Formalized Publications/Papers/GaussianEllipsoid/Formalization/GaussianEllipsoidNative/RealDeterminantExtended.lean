import CappedDeterminantExtended
import RealDeterminantExpectation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section
open MeasureTheory Matrix Finset Set Filter
open scoped Topology

namespace GaussianEllipsoid.CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Extended inverse determinant power. A singular covariance contributes
`∞` whenever the real exponent is positive. -/
def extendedRealDetInv (s : ℝ) (A : Matrix ι ι ℝ) : ENNReal :=
  (ENNReal.ofReal A.det ^ s)⁻¹

def extendedRealMoment (μ : Measure (κ → ι → ℝ)) (s : ℝ) (w : κ → ℝ) : ENNReal :=
  ∫⁻ g, extendedRealDetInv s (weightedGram g w) ∂μ

/-- Checked singular convention, unlike real-valued inversion at zero. -/
theorem extendedRealDetInv_of_det_zero (s : ℝ) (hs : 0 < s) {A : Matrix ι ι ℝ}
    (hA : A.det = 0) : extendedRealDetInv s A = ⊤ := by
  simp [extendedRealDetInv, hA, ENNReal.zero_rpow_of_pos hs]

/-- On positive determinants, the extended and real integrands agree. -/
theorem ofReal_det_neg_rpow {A : Matrix ι ι ℝ} (hA : 0 < A.det) (s : ℝ) :
    ENNReal.ofReal (A.det ^ (-s)) = extendedRealDetInv s A := by
  rw [Real.rpow_neg hA.le, ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hA s)]
  rw [extendedRealDetInv, ENNReal.ofReal_rpow_of_pos hA]

/-- Pointwise monotonicity of the extended regularized integrands. -/
theorem monotone_extended_real_regularized (g : κ → ι → ℝ) {w : κ → ℝ}
    (hw : ∀ k, 0 ≤ w k) (s : ℝ) (hs : 0 ≤ s) :
    Monotone (fun n => extendedRealDetInv s (regularizedGram (ridgeSeq n) g w)) := by
  intro n m hnm
  simp only [extendedRealDetInv]
  apply ENNReal.inv_le_inv.mpr
  apply ENNReal.rpow_le_rpow _ hs
  apply ENNReal.ofReal_le_ofReal
  exact det_scalar_add_posSemidef_mono (weightedGram_posSemidef g hw)
    (le_of_lt (ridgeSeq_pos m)) (ridgeSeq_antitone hnm)

/-- The pointwise limit includes singular covariances with the correct
infinite value, by continuity of inversion on the extended nonnegative reals. -/
theorem tendsto_extended_real_regularized (g : κ → ι → ℝ) (w : κ → ℝ) (s : ℝ) :
    Tendsto (fun n => extendedRealDetInv s (regularizedGram (ridgeSeq n) g w))
      atTop (𝓝 (extendedRealDetInv s (weightedGram g w))) := by
  have hdet : Continuous (fun ε : ℝ => (regularizedGram ε g w).det) := by
    apply Continuous.matrix_det
    unfold regularizedGram
    fun_prop
  have hcont := ((ENNReal.continuous_rpow_const (y := s)).comp
    (ENNReal.continuous_ofReal.comp hdet)).inv
  have hlim := (hcont.tendsto 0).comp ridgeSeq_tendsto
  simpa only [Function.comp_def, Pi.inv_apply, extendedRealDetInv, regularizedGram, zero_smul, zero_add] using hlim

/-- Every extended regularized moment equals the embedding of a genuinely
integrable real expectation. -/
theorem ofReal_regularizedRealMoment_eq_lintegral
    (μ : Measure (κ → ι → ℝ)) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (s : ℝ) (hs : 0 ≤ s) :
    ENNReal.ofReal (regularizedRealMoment μ ε s w) =
      ∫⁻ g, extendedRealDetInv s (regularizedGram ε g w) ∂μ := by
  unfold regularizedRealMoment
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_regularized_det_neg_rpow μ hε hw s hs)
    (Filter.Eventually.of_forall (fun g =>
      le_of_lt (Real.rpow_pos_of_pos (regularizedGram_posDef hε g hw).det_pos _)))]
  apply lintegral_congr_ae
  filter_upwards [] with g
  exact ofReal_det_neg_rpow (regularizedGram_posDef hε g hw).det_pos s

/-- Monotone convergence transfers the entire regularized expectation to the
extended inverse determinant moment without an invertibility assumption. -/
theorem tendsto_ofReal_regularizedRealMoment
    (μ : Measure (κ → ι → ℝ)) [IsFiniteMeasure μ] {w : κ → ℝ}
    (hw : ∀ k, 0 ≤ w k) (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun n => ENNReal.ofReal (regularizedRealMoment μ (ridgeSeq n) s w))
      atTop (𝓝 (extendedRealMoment μ s w)) := by
  have hm : ∀ n, Measurable (fun g : κ → ι → ℝ =>
      extendedRealDetInv s (regularizedGram (ridgeSeq n) g w)) := by
    intro n
    have hc := ENNReal.continuous_ofReal.comp
      (continuous_regularized_det_neg_rpow (ι := ι) (ridgeSeq_pos n) hw s hs)
    have heq : (fun g : κ → ι → ℝ =>
        extendedRealDetInv s (regularizedGram (ridgeSeq n) g w)) =
        (fun g => ENNReal.ofReal ((regularizedGram (ridgeSeq n) g w).det ^ (-s))) := by
      funext g
      exact (ofReal_det_neg_rpow (regularizedGram_posDef (ridgeSeq_pos n) g hw).det_pos s).symm
    rw [heq]
    exact hc.measurable
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (fun n => (hm n).aemeasurable)
    (Filter.Eventually.of_forall (fun g => monotone_extended_real_regularized g hw s hs))
    (Filter.Eventually.of_forall (fun g => tendsto_extended_real_regularized g w s))
  convert hlim using 1
  · funext n
    exact ofReal_regularizedRealMoment_eq_lintegral μ (ridgeSeq_pos n) hw s hs
  · rfl


end GaussianEllipsoid.CappedSimplex
