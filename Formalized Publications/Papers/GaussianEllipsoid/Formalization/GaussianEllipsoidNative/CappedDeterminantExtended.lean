import RegularizedExpectationSymmetry
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section
open MeasureTheory Matrix Finset Set Filter
open scoped Topology

namespace GaussianEllipsoid.CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Extended inverse determinant power. A singular covariance contributes
`∞` whenever the natural exponent is positive. -/
def extendedDetInv (s : ℕ) (A : Matrix ι ι ℝ) : ENNReal :=
  (ENNReal.ofReal A.det ^ s)⁻¹

def extendedMoment (μ : Measure (κ → ι → ℝ)) (s : ℕ) (w : κ → ℝ) : ENNReal :=
  ∫⁻ g, extendedDetInv s (weightedGram g w) ∂μ

/-- Checked singular convention, unlike real-valued inversion at zero. -/
theorem extendedDetInv_of_det_zero (s : ℕ) (hs : 0 < s) {A : Matrix ι ι ℝ}
    (hA : A.det = 0) : extendedDetInv s A = ⊤ := by
  simp [extendedDetInv, hA, _root_.zpow_neg, zpow_natCast, ne_of_gt hs]

/-- On positive determinants, the extended and real integrands agree. -/
theorem ofReal_det_neg_nat_zpow {A : Matrix ι ι ℝ} (hA : 0 < A.det) (s : ℕ) :
    ENNReal.ofReal (A.det ^ (-(s : ℤ))) = extendedDetInv s A := by
  simp only [extendedDetInv, _root_.zpow_neg, zpow_natCast]
  rw [ENNReal.ofReal_inv_of_pos (pow_pos hA s), ENNReal.ofReal_pow (le_of_lt hA)]

/-- The determinant increases with the nonnegative scalar ridge. -/
theorem det_scalar_add_posSemidef_mono {H : Matrix ι ι ℝ} (hH : H.PosSemidef)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (x • (1 : Matrix ι ι ℝ) + H).det ≤ (y • (1 : Matrix ι ι ℝ) + H).det := by
  rw [det_scalar_add_posSemidef hH x, det_scalar_add_posSemidef hH y]
  exact Finset.prod_le_prod
    (fun i _ => add_nonneg hx (hH.eigenvalues_nonneg i))
    (fun i _ => add_le_add_left hxy _)

/-- Fixed positive ridges decreasing to zero. -/
def ridgeSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem ridgeSeq_pos (n : ℕ) : 0 < ridgeSeq n := by unfold ridgeSeq; positivity

theorem ridgeSeq_antitone : Antitone ridgeSeq := by
  intro n m hnm
  simp only [ridgeSeq, one_div]
  apply inv_anti₀ (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 1

theorem ridgeSeq_tendsto : Tendsto ridgeSeq atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Pointwise monotonicity of the extended regularized integrands. -/
theorem monotone_extended_regularized (g : κ → ι → ℝ) {w : κ → ℝ}
    (hw : ∀ k, 0 ≤ w k) (s : ℕ) :
    Monotone (fun n => extendedDetInv s (regularizedGram (ridgeSeq n) g w)) := by
  intro n m hnm
  simp only [extendedDetInv, _root_.zpow_neg, zpow_natCast]
  apply ENNReal.inv_le_inv.mpr
  apply pow_le_pow_left'
  apply ENNReal.ofReal_le_ofReal
  exact det_scalar_add_posSemidef_mono (weightedGram_posSemidef g hw)
    (le_of_lt (ridgeSeq_pos m)) (ridgeSeq_antitone hnm)

/-- The pointwise limit includes singular covariances with the correct
infinite value, by continuity of inversion on the extended nonnegative reals. -/
theorem tendsto_extended_regularized (g : κ → ι → ℝ) (w : κ → ℝ) (s : ℕ) :
    Tendsto (fun n => extendedDetInv s (regularizedGram (ridgeSeq n) g w))
      atTop (𝓝 (extendedDetInv s (weightedGram g w))) := by
  have hdet : Continuous (fun ε : ℝ => (regularizedGram ε g w).det) := by
    apply Continuous.matrix_det
    unfold regularizedGram
    fun_prop
  have hcont := ((ENNReal.continuous_pow s).comp
    (ENNReal.continuous_ofReal.comp hdet)).inv
  have hlim := (hcont.tendsto 0).comp ridgeSeq_tendsto
  simpa only [Function.comp_def, Pi.inv_apply, extendedDetInv, regularizedGram, zero_smul, zero_add] using hlim

/-- Every extended regularized moment equals the embedding of a genuinely
integrable real expectation. -/
theorem ofReal_regularizedMoment_eq_lintegral
    (μ : Measure (κ → ι → ℝ)) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (s : ℕ) :
    ENNReal.ofReal (regularizedMoment μ ε s w) =
      ∫⁻ g, extendedDetInv s (regularizedGram ε g w) ∂μ := by
  unfold regularizedMoment
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_regularized_det_neg_nat_zpow μ hε hw s)
    (Filter.Eventually.of_forall (fun g =>
      le_of_lt (zpow_pos (regularizedGram_posDef hε g hw).det_pos _)))]
  apply lintegral_congr_ae
  filter_upwards [] with g
  exact ofReal_det_neg_nat_zpow (regularizedGram_posDef hε g hw).det_pos s

/-- Monotone convergence transfers the entire regularized expectation to the
extended inverse determinant moment without an invertibility assumption. -/
theorem tendsto_ofReal_regularizedMoment
    (μ : Measure (κ → ι → ℝ)) [IsFiniteMeasure μ] {w : κ → ℝ}
    (hw : ∀ k, 0 ≤ w k) (s : ℕ) :
    Tendsto (fun n => ENNReal.ofReal (regularizedMoment μ (ridgeSeq n) s w))
      atTop (𝓝 (extendedMoment μ s w)) := by
  have hm : ∀ n, Measurable (fun g : κ → ι → ℝ =>
      extendedDetInv s (regularizedGram (ridgeSeq n) g w)) := by
    intro n
    have hc := ENNReal.continuous_ofReal.comp
      (continuous_regularized_det_neg_nat_zpow (ι := ι) (ridgeSeq_pos n) hw s)
    have heq : (fun g : κ → ι → ℝ =>
        extendedDetInv s (regularizedGram (ridgeSeq n) g w)) =
        (fun g => ENNReal.ofReal ((regularizedGram (ridgeSeq n) g w).det ^ (-(s : ℤ)))) := by
      funext g
      exact (ofReal_det_neg_nat_zpow (regularizedGram_posDef (ridgeSeq_pos n) g hw).det_pos s).symm
    rw [heq]
    exact hc.measurable
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (fun n => (hm n).aemeasurable)
    (Filter.Eventually.of_forall (fun g => monotone_extended_regularized g hw s))
    (Filter.Eventually.of_forall (fun g => tendsto_extended_regularized g w s))
  convert hlim using 1
  · funext n
    exact ofReal_regularizedMoment_eq_lintegral μ (ridgeSeq_pos n) hw s
  · rfl

/-- Capped determinant extremization, fully extended-valued and valid even
when either moment is infinite. This is the exact endpoint cap used in the
small-ball proof, for every natural inverse exponent. -/
theorem extendedMoment_le_fixed_uniform_subset
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (s m : ℕ) (hm : 0 < m) {w : κ → ℝ} (hw : w ∈ slice ((m : ℝ)⁻¹) 1)
    (T : Finset κ) (hT : T.card = m) :
    extendedMoment (Measure.pi (fun _ : κ => μ)) s w ≤
      extendedMoment (Measure.pi (fun _ : κ => μ)) s
        (fun i => if i ∈ T then (m : ℝ)⁻¹ else 0) := by
  have hTw : ∀ i : κ, 0 ≤ (if i ∈ T then (m : ℝ)⁻¹ else 0) := by
    intro i
    split_ifs <;> positivity
  apply le_of_tendsto_of_tendsto
    (tendsto_ofReal_regularizedMoment (Measure.pi (fun _ : κ => μ)) (fun i => (hw.1 i).1) s)
    (tendsto_ofReal_regularizedMoment (Measure.pi (fun _ : κ => μ)) hTw s)
  filter_upwards [] with n
  exact ENNReal.ofReal_le_ofReal
    (regularizedMoment_le_fixed_uniform_subset μ (ridgeSeq_pos n) s m hm hw T hT)

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.extendedMoment_le_fixed_uniform_subset
#print axioms GaussianEllipsoid.CappedSimplex.extendedDetInv_of_det_zero
