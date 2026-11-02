import BMSaddleProbability
import BMHighProbabilityBox

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal Matrix
open GaussianEllipsoid BMGeometry GaussianTensorMoments GaussianMixedNormHelpers MeasureTheory ProbabilityTheory
namespace BMSaddle

abbrev Raw (n d : ℕ) := Fin n → Fin (d*d) → ℝ
abbrev rawSourceLaw (n d : ℕ) := Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))

def rawSample (n d : ℕ) (z : Raw n d) : Sample n d :=
  (WithLp.equiv 2 _).symm (fun p => z p.1 (finProdFinEquiv p.2))

/-- Exact joint law transport from the literal independent BM adapter-row source. -/
theorem rawSample_preserving (n d : ℕ) :
    MeasurePreserving (rawSample n d) (rawSourceLaw n d) (sampleLaw n d) := by
  have hrow : MeasurePreserving (fun z : Fin (d*d) → ℝ => fun p : Fin d × Fin d => z (finProdFinEquiv p))
      (gaussianProductLaw (Fin (d*d))) (gaussianProductLaw (Fin d × Fin d)) := by
    convert! measurePreserving_piCongrLeft (fun _ : Fin d × Fin d => gaussianReal 0 1) finProdFinEquiv.symm using 1
    ext z p
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hrows := measurePreserving_pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))
    (fun _ : Fin n => gaussianProductLaw (Fin d × Fin d)) (fun _ => hrow)
  have hc : MeasurePreserving (fun z : Fin n → (Fin d × Fin d) → ℝ => fun p : EntryIndex n d => z p.1 p.2)
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin d × Fin d))) (gaussianProductLaw (EntryIndex n d)) :=
    ⟨by fun_prop, gaussianProductColumns_map_uncurry⟩
  have he : MeasurePreserving (MeasurableEquiv.toLp 2 ((EntryIndex n d) → ℝ))
      (gaussianProductLaw (EntryIndex n d)) (sampleLaw n d) :=
    ⟨(MeasurableEquiv.toLp 2 ((EntryIndex n d) → ℝ)).measurable,rfl⟩
  exact he.comp (hc.comp hrows)

def statisticRaw (n d : ℕ) (κ R : ℝ) (z : Raw n d) : ℝ := statistic n d κ R (rawSample n d z)

theorem statisticRaw_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) :
    Integrable (statisticRaw n d κ R) (rawSourceLaw n d) :=
  ((rawSample_preserving n d).integrable_comp (statistic_continuous hn hd hκ R).aestronglyMeasurable).mpr
    (statistic_integrable hn hd hκ R)

theorem statisticRaw_mean {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) :
    (∫ z, statisticRaw n d κ R z ∂rawSourceLaw n d) = statisticMean n d κ R := by
  have h := integral_map (rawSample_preserving n d).measurable.aemeasurable
    (f := statistic n d κ R) (by
      rw [(rawSample_preserving n d).map_eq]
      exact (statistic_continuous hn hd hκ R).aestronglyMeasurable)
  rw [(rawSample_preserving n d).map_eq] at h
  exact h.symm

theorem statisticRaw_negative_tail {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ R c : ℝ}
    (hκ : 1 ≤ κ) (hc : 0 < c) (hmean : c*d ≤ statisticMean n d κ R) :
    (rawSourceLaw n d).real {z | statisticRaw n d κ R z < 0} ≤ Real.pi^2/(8*c^2*(d:ℝ)^2) := by
  rw [show {z | statisticRaw n d κ R z < 0} = rawSample n d ⁻¹' {X | statistic n d κ R X < 0} from rfl,
    (rawSample_preserving n d).measureReal_preimage
      ((isOpen_lt (statistic_continuous hn hd hκ R) continuous_const).measurableSet.nullMeasurableSet)]
  exact statistic_negative_tail hn hd hκ hc hmean

/-- Literal adapter trace equals the standard full-entry measurement times the BM scale. -/
theorem actual_trace_measurement {n d : ℕ} (z : Raw n d) (S : Op d) (hS : IsPSD S) (k : Fin n) :
    Matrix.trace (BMGaussianEquivalent.symmetrizedGaussianMatrix d (z k) * opMatrix S) =
      Real.sqrt (2/(d:ℝ)) * measurement (rawSample n d z) (operatorFrobenius S) k := by
  have hsym : (opMatrix S).transpose = opMatrix S := by
    ext i j
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) ((opMatrix_posSemidef_iff S).mpr hS).1
    simpa only [Matrix.transpose_apply,Matrix.conjTranspose_apply,star_trivial] using h
  rw [BMGaussianEquivalent.trace_symmetrizedGaussianMatrix_mul _ hsym,
    BMGaussianEquivalent.eval_gaussianCoefficients, measurement_apply]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  change operatorFrobenius S j i * z k (finProdFinEquiv (i,j)) =
    z k (finProdFinEquiv (i,j)) * operatorFrobenius S j i
  ring

/-- The actual BM-scaled exact-fit event follows from a nonnegative saddle value.
The constructed Frobenius norm is at most R sqrt(d/2), hence at most R sqrt d. -/
theorem actualConeFeasible_of_statisticRaw_nonneg {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {κ R : ℝ} (hκ : 1 ≤ κ) (hR : 0 < R) (z : Raw n d)
    (hF : 0 ≤ statisticRaw n d κ R z) : BMSpectralBridge.actualConeFeasible n d κ R z := by
  obtain ⟨S,hS,hnorm,hfit⟩ := affine_feasible_of_statistic_nonneg hn hd hκ hR (rawSample n d z) hF
  let a : ℝ := Real.sqrt ((d:ℝ)/2)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  refine ⟨a • S,conditionCone_smul ha hS,?_,?_⟩
  · rw [operatorFrobenius_smul, norm_smul, Real.norm_eq_abs,abs_of_nonneg ha]
    calc
      a*‖operatorFrobenius S‖ ≤ a*R := mul_le_mul_of_nonneg_left hnorm ha
      _ ≤ R*Real.sqrt d := by
        have hs : a ≤ Real.sqrt d := by
          change Real.sqrt ((d:ℝ)/2) ≤ Real.sqrt (d:ℝ)
          exact Real.sqrt_le_sqrt (by nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
        nlinarith
  · intro k
    rw [actual_trace_measurement z (a • S) (conditionCone_smul ha hS).1 k,
      operatorFrobenius_smul, map_smul, hfit]
    change Real.sqrt (2/(d:ℝ)) * (a*1) = 1
    rw [mul_one]
    have hd' : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
    have hp : (2/(d:ℝ))*((d:ℝ)/2) = 1 := by field_simp
    dsimp only [a]
    rw [← Real.sqrt_mul (by positivity),hp,Real.sqrt_one]

/-- Explicit probability bound for failure of the actual original Gaussian-cone event. -/
theorem actualCone_failure_le_mean_tail {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ R c : ℝ}
    (hκ : 1 ≤ κ) (hR : 0 < R) (hc : 0 < c) (hmean : c*d ≤ statisticMean n d κ R) :
    (rawSourceLaw n d).real {z | ¬BMSpectralBridge.actualConeFeasible n d κ R z} ≤
      Real.pi^2/(8*c^2*(d:ℝ)^2) := by
  apply (measureReal_mono (show {z | ¬BMSpectralBridge.actualConeFeasible n d κ R z} ⊆
    {z | statisticRaw n d κ R z < 0} from ?_)).trans (statisticRaw_negative_tail hn hd hκ hc hmean)
  intro z hz
  by_contra hneg
  exact hz (actualConeFeasible_of_statisticRaw_nonneg hn hd hκ hR z (le_of_not_gt hneg))

end BMSaddle
