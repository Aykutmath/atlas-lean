import BMBoxRiskTransfer

/-!
# Physical real-power risk and exact BM trace rescaling

This file extends the frozen r=1 layer without editing it.  Every exponent uses
the same actual Loewner box; only the tolerance changes with the exponent.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
open MeasureTheory Filter GaussianTensorMoments GaussianMixedNormHelpers
open BMUniformMoment BMQuadraticSpectral BMSymmetricFiniteUniversality
open scoped BigOperators

namespace BMBoxRiskAssembly

/-- Actual empirical real-power loss. No root of the empirical average is taken. -/
def empiricalPower {n : ℕ} (r : ℝ) (y : Fin n → ℝ) : ℝ :=
  (1/(n:ℝ))*∑ i, |y i|^r

/-- Original physical fitting risk at real exponent r. -/
def fittingRisk {d n : ℕ} (r : ℝ) (S : BMRescaling.Square d)
    (x : CoordinateSample d n) : ℝ :=
  empiricalPower r (fun i => BMRescaling.fittingResidual S (x i))

/-- The original BM interface's literal real-power risk expression. -/
theorem fittingRisk_eq_original {d n : ℕ} (r : ℝ) (S : BMRescaling.Square d)
    (x : CoordinateSample d n) :
    fittingRisk r S x = (1/(n:ℝ))*∑ i,
      |(BMRescaling.quadratic S (x i)-(d:ℝ))/Real.sqrt (d:ℝ)|^r := rfl

/-- The new real-power loss specializes exactly to the frozen r=1 loss. -/
theorem fittingRisk_one {d n : ℕ} (S : BMRescaling.Square d) (x : CoordinateSample d n) :
    fittingRisk 1 S x = fittingL1 S x := by
  simp only [fittingRisk, empiricalPower, Real.rpow_one, fittingL1, BMRescaling.empiricalL1]

/-- Exact scaling of every real-power empirical risk under BM's trace normalization. -/
theorem empiricalPower_rescale {d n : ℕ} (hd : 0 < d) {lo hi : ℝ}
    {S : BMRescaling.Square d} (hlo : 0 < lo)
    (hS : S ∈ BMRescaling.spectralBox d lo hi) (x : CoordinateSample d n) (r : ℝ) :
    fittingRisk r (BMRescaling.rescale S) x =
      (BMRescaling.scale S)^r *
        empiricalPower r (fun i => BMRescaling.centeredResidual S (x i)) := by
  unfold fittingRisk empiricalPower
  simp_rw [BMRescaling.fittingResidual_rescale hd hlo hS, abs_mul,
    abs_of_pos (BMRescaling.scale_pos hd hlo hS),
    Real.mul_rpow (BMRescaling.scale_pos hd hlo hS).le (abs_nonneg _)]
  rw [← Finset.mul_sum]
  ring

/-- The same fixed positive box controls physical r-risk by lo^(-r), for all
nonnegative exponents. -/
theorem empiricalPower_rescale_le {d n : ℕ} (hd : 0 < d) {lo hi : ℝ}
    {S : BMRescaling.Square d} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hS : S ∈ BMRescaling.spectralBox d lo hi) (x : CoordinateSample d n)
    {r : ℝ} (hr : 0 ≤ r) :
    fittingRisk r (BMRescaling.rescale S) x ≤
      empiricalPower r (fun i => BMRescaling.centeredResidual S (x i)) / lo^r := by
  rw [empiricalPower_rescale hd hlo hS]
  have hnonneg : 0 ≤ empiricalPower r (fun i => BMRescaling.centeredResidual S (x i)) := by
    unfold empiricalPower
    positivity
  have hscale := Real.rpow_le_rpow (BMRescaling.scale_pos hd hlo hS).le
    (BMRescaling.scale_bounds hd hlo hlohi hS).2 hr
  have h := mul_le_mul_of_nonneg_right hscale hnonneg
  have hpow : (1/lo)^r = 1/lo^r := by
    rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 1) hlo.le, Real.one_rpow]
  rw [hpow] at h
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

/-- Exact centered real-power loss in the original Gaussian coordinates. -/
theorem centered_empiricalPower_eq {d n : ℕ} (r : ℝ) (T : SymOp d)
    (x : CoordinateSample d n) :
    empiricalPower r (fun i => BMRescaling.centeredResidual (matrixOf T) (x i)) =
      (∑ i, |normalizedQuadratic T.val (sampleEuclideanEquiv d n x i)-1|^r)/(n:ℝ) := by
  simp only [sampleEuclideanEquiv_apply, normalizedQuadratic_sub_one_eq_centeredResidual,
    empiricalPower, one_div, div_eq_mul_inv]
  ring

/-- Physical fitting with an r-th power empirical-loss tolerance. -/
def fittingFeasibleR (d n : ℕ) (lo hi r ε : ℝ) (x : CoordinateSample d n) : Prop :=
  ∃ S ∈ BMRescaling.spectralBox d lo hi, fittingRisk r S x < ε

/-- Actual physical r-risk fitting failure probability. -/
def fittingFailureProbabilityR (d n : ℕ) (lo hi r ε : ℝ) : ℝ :=
  (coordinateSampleLaw d n).real {x | ¬fittingFeasibleR d n lo hi r ε x}

/-- The exact original BM real-power infimum risk. -/
def minFittingRisk (d n : ℕ) (x : CoordinateSample d n) (lo hi r : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ S ∈ BMRescaling.spectralBox d lo hi, t = fittingRisk r S x}

/-- Literal expansion, matching the original bmMinRisk formula. -/
theorem minFittingRisk_eq_original (d n : ℕ) (x : CoordinateSample d n) (lo hi r : ℝ) :
    minFittingRisk d n x lo hi r = sInf {t : ℝ |
      ∃ S ∈ BMRescaling.spectralBox d lo hi,
        t = (1/(n:ℝ))*∑ i,
          |(BMRescaling.quadratic S (x i)-(d:ℝ))/Real.sqrt (d:ℝ)|^r} := rfl

/-- Agreement with the already audited r=1 infimum. -/
theorem minFittingRisk_one (d n : ℕ) (x : CoordinateSample d n) (lo hi : ℝ) :
    minFittingRisk d n x lo hi 1 = minFittingRiskOne d n x lo hi := by
  simp only [minFittingRisk, minFittingRiskOne, fittingRisk_one]

/-- A physical fitting witness bounds the infimum without an attainment hypothesis. -/
theorem minFittingRisk_le {d n : ℕ} (x : CoordinateSample d n) (r : ℝ) {lo hi : ℝ}
    {S : BMRescaling.Square d} (hS : S ∈ BMRescaling.spectralBox d lo hi) :
    minFittingRisk d n x lo hi r ≤ fittingRisk r S x := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨T, hT, rfl⟩
    unfold fittingRisk empiricalPower
    positivity
  · exact ⟨S,hS,rfl⟩

/-- Failure of the original infimum-risk bound requires failure of every strict fit. -/
theorem minRiskR_failure_subset (d n : ℕ) (lo hi r ε : ℝ) :
    {x : CoordinateSample d n | ε < minFittingRisk d n x lo hi r} ⊆
      {x | ¬fittingFeasibleR d n lo hi r ε x} := by
  intro x hx hfit
  obtain ⟨S,hS,hfit⟩ := hfit
  exact (not_lt_of_ge ((minFittingRisk_le x r hS).trans hfit.le)) hx

/-- Transfer from strict physical fitting failure to the exact original risk tail. -/
theorem minRiskR_tendsto_zero_of_fitting_failure (n : ℕ → ℕ) (lo hi r ε : ℝ)
    (h : Tendsto (fun d => fittingFailureProbabilityR d (n d) lo hi r ε) atTop (nhds 0)) :
    Tendsto (fun d => (coordinateSampleLaw d (n d)).real
      {x | ε < minFittingRisk d (n d) x lo hi r}) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _ h
  intro d
  exact measureReal_mono (minRiskR_failure_subset d (n d) lo hi r ε)

/-- The complete original exponent range, on one fixed spectral box. -/
def BMminRiskAllR (n : ℕ → ℕ) (lo hi : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → r < 4/3 → ∀ ε > 0,
    Tendsto (fun d => (coordinateSampleLaw d (n d)).real
      {x | ε < minFittingRisk d (n d) x lo hi r}) atTop (nhds 0)

/-- A centered r-fit gives a physical r-fit in the same exponent-independent
rescaled box; the tolerance is multiplied by lo^r. -/
theorem fittingFeasibleR_of_centered {d n : ℕ} (hd : 0 < d) {lo hi r ε : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hr : 0 ≤ r) (x : CoordinateSample d n)
    (hfit : ∃ T ∈ operatorBox d lo hi,
      (∑ i, |normalizedQuadratic T.val (sampleEuclideanEquiv d n x i)-1|^r)/(n:ℝ)
        < ε*lo^r) :
    fittingFeasibleR d n (lo/(hi+1)) (hi/lo) r ε x := by
  obtain ⟨T,hT,hrisk⟩ := hfit
  refine ⟨BMRescaling.rescale (matrixOf T),
    BMRescaling.rescale_mem_fixed_box hd hlo hlohi hT, ?_⟩
  have hbound := empiricalPower_rescale_le hd hlo hlohi hT x hr
  exact hbound.trans_lt ((div_lt_iff₀ (Real.rpow_pos_of_pos hlo r)).mpr (by
    simpa only [centered_empiricalPower_eq] using hrisk))

/-- Nonnegativity of the literal infimum risk in every nonempty ordered box. -/
theorem minFittingRisk_nonneg (d n : ℕ) (x : CoordinateSample d n) (lo hi r : ℝ)
    (hlohi : lo ≤ hi) : 0 ≤ minFittingRisk d n x lo hi r := by
  apply le_csInf
  · exact ⟨_,_,lower_identity_mem_spectralBox d hlohi,rfl⟩
  · rintro t ⟨S,hS,rfl⟩
    unfold fittingRisk empiricalPower
    positivity

/-- Strict slack provides an actual fitting witness, without compactness,
attainment, or a measurable selector. -/
theorem minFittingRisk_lt_iff {d n : ℕ} (x : CoordinateSample d n) {lo hi r δ : ℝ}
    (hlohi : lo ≤ hi) :
    minFittingRisk d n x lo hi r < δ ↔
      ∃ S ∈ BMRescaling.spectralBox d lo hi, fittingRisk r S x < δ := by
  constructor
  · intro h
    have hne : {t : ℝ | ∃ S ∈ BMRescaling.spectralBox d lo hi,
        t = fittingRisk r S x}.Nonempty :=
      ⟨_,_,lower_identity_mem_spectralBox d hlohi,rfl⟩
    obtain ⟨t,⟨S,hS,rfl⟩,ht⟩ := exists_lt_of_csInf_lt hne h
    exact ⟨S,hS,ht⟩
  · rintro ⟨S,hS,hfit⟩
    exact (minFittingRisk_le x r hS).trans_lt hfit

/-- Finite-sample physical r-loss is continuous for all r ≥ 0. -/
theorem continuous_fittingRisk {d n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (S : BMRescaling.Square d) :
    Continuous (fun x : CoordinateSample d n => fittingRisk r S x) := by
  unfold fittingRisk empiricalPower BMRescaling.fittingResidual BMRescaling.quadratic
  simp only [dotProduct, Matrix.mulVec]
  fun_prop (disch := positivity)

/-- Physical strict-fit failure is closed for every allowed exponent. -/
theorem isClosed_fittingR_failure_event (d n : ℕ) (lo hi r ε : ℝ) (hr : 0 ≤ r) :
    IsClosed {x : CoordinateSample d n | ¬fittingFeasibleR d n lo hi r ε x} := by
  have hclosed := isClosed_iInter (fun S : BMRescaling.Square d =>
    isClosed_iInter (fun _hS : S ∈ BMRescaling.spectralBox d lo hi =>
      isClosed_le (continuous_const : Continuous (fun _ : CoordinateSample d n => ε))
        (continuous_fittingRisk hr S)))
  convert hclosed using 1
  ext x
  simp only [fittingFeasibleR, Set.mem_iInter, Set.mem_setOf_eq, not_exists, not_and, not_lt]

/-- Physical r-fit failure is a measurable event. -/
theorem measurableSet_fittingR_failure_event (d n : ℕ) (lo hi r ε : ℝ) (hr : 0 ≤ r) :
    MeasurableSet {x : CoordinateSample d n | ¬fittingFeasibleR d n lo hi r ε x} :=
  (isClosed_fittingR_failure_event d n lo hi r ε hr).measurableSet

/-- The literal infimum risk is measurable for every allowed real exponent. -/
theorem measurable_minFittingRisk (d n : ℕ) (lo hi r : ℝ) (hr : 0 ≤ r) :
    Measurable (fun x : CoordinateSample d n => minFittingRisk d n x lo hi r) := by
  letI : NormedAddCommGroup (BMRescaling.Square d) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (BMRescaling.Square d) := Matrix.normedSpace
  have hcont (S : BMRescaling.Square d) (_hS : S ∈ BMRescaling.spectralBox d lo hi) :
      Continuous (fun x : CoordinateSample d n => fittingRisk r S x) := continuous_fittingRisk hr S
  have hbelow (x : CoordinateSample d n) : BddBelow
      ((fun S : BMRescaling.Square d => fittingRisk r S x) '' BMRescaling.spectralBox d lo hi) := by
    refine ⟨0, ?_⟩
    rintro t ⟨S,hS,rfl⟩
    unfold fittingRisk empiricalPower
    positivity
  have h := BMNetGroundExtension.measurable_ground_of_continuous
    (BMRescaling.spectralBox d lo hi) (fun x S => fittingRisk r S x) hcont hbelow
  have heq (x : CoordinateSample d n) : minFittingRisk d n x lo hi r =
      BMNetGroundExtension.ground (BMRescaling.spectralBox d lo hi) (fun S => fittingRisk r S x) := by
    unfold minFittingRisk BMNetGroundExtension.ground
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor <;> rintro ⟨S,hS,ht⟩ <;> exact ⟨S,hS,ht.symm⟩
  simp_rw [heq]
  exact h

/-- Original real-power risk tails are actual measurable events. -/
theorem measurableSet_minRiskR_tail (d n : ℕ) (lo hi r ε : ℝ) (hr : 0 ≤ r) :
    MeasurableSet {x : CoordinateSample d n | ε < minFittingRisk d n x lo hi r} :=
  measurableSet_lt measurable_const (measurable_minFittingRisk d n lo hi r hr)

end BMBoxRiskAssembly
