import BMCoordinateSampleLawCore
import BMGaussianFeasibilityTransfer
import BMHighProbabilityBox

/-!
# Exact ordinary-coordinate source and residual bridges

All random variables use the actual standard Gaussian product law.  The
ordinary-coordinate residual is the original physical fitting residual,
not the centered rank-one observable used inside the universality theorem.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
open MeasureTheory Filter GaussianTensorMoments GaussianMixedNormHelpers
open BMUniformMoment BMQuadraticSpectral BMSymmetricFiniteUniversality
open scoped BigOperators

namespace BMBoxRiskAssembly

/-- The coordinate matrix quadratic is exactly the centered trace observation. -/
theorem matrixQuadratic_eq_centeredObservation {d : ℕ}
    (S : BMRescaling.Square d) (x : Fin d → ℝ) :
    matrixQuadratic S x = Matrix.trace (BMRescaling.centeredObservation x * S) := by
  have hq : (∑ i, ∑ j, S i j * (x i * x j)) = BMRescaling.quadratic S x := by
    simp only [BMRescaling.quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hr := BMRescaling.centeredResidual_eq S x
  unfold BMRescaling.centeredResidual at hr
  unfold matrixQuadratic
  rw [hq]
  linarith

/-- Pointwise identity between the universality residual and BM's centered
rank-one residual, in the actual original Gaussian coordinates. -/
theorem normalizedQuadratic_sub_one_eq_centeredResidual {d : ℕ}
    (T : SymOp d) (x : Fin d → ℝ) :
    normalizedQuadratic T.val ((MeasurableEquiv.toLp 2 ((Fin d) → ℝ)) x) - 1 =
      BMRescaling.centeredResidual (matrixOf T) x := by
  rw [← toEuclideanCLM_matrixOf T]
  have hm := normalizedQuadratic_matrix_eq (matrixOf T) x
  simp only [MeasurableEquiv.symm_symm] at hm
  rw [hm, matrixQuadratic_eq_centeredObservation]
  rfl

/-- Finite L1 risk is the same average used by the continuum transfer. -/
theorem centered_empiricalL1_eq {d n : ℕ} (T : SymOp d) (x : CoordinateSample d n) :
    BMRescaling.empiricalL1 (fun i => BMRescaling.centeredResidual (matrixOf T) (x i)) =
      (∑ i, |normalizedQuadratic T.val (sampleEuclideanEquiv d n x i)-1|)/(n:ℝ) := by
  simp only [sampleEuclideanEquiv_apply, normalizedQuadratic_sub_one_eq_centeredResidual,
    BMRescaling.empiricalL1, one_div, div_eq_mul_inv]
  ring

/-- Literal physical L1 fitting risk. -/
def fittingL1 {d n : ℕ} (S : BMRescaling.Square d) (x : CoordinateSample d n) : ℝ :=
  BMRescaling.empiricalL1 (fun i => BMRescaling.fittingResidual S (x i))

/-- The r=1 instance of the original real-power risk, with the displayed
quadratic/sqrt(d) residual and ordinary-coordinate iid Gaussian samples. -/
theorem fittingL1_eq_rpow_one {d n : ℕ} (S : BMRescaling.Square d)
    (x : CoordinateSample d n) :
    fittingL1 S x = (1/(n:ℝ))*∑ i,
      |(BMRescaling.quadratic S (x i)-(d:ℝ))/Real.sqrt (d:ℝ)|^(1:ℝ) := by
  simp only [fittingL1, BMRescaling.empiricalL1, BMRescaling.fittingResidual, Real.rpow_one]

/-- Original fitting success at a fixed positive spectral box. -/
def fittingFeasible (d n : ℕ) (lo hi ε : ℝ) (x : CoordinateSample d n) : Prop :=
  ∃ S ∈ BMRescaling.spectralBox d lo hi, fittingL1 S x < ε

/-- Actual outer failure probability of physical L1 fitting. -/
def fittingFailureProbability (d n : ℕ) (lo hi ε : ℝ) : ℝ :=
  (coordinateSampleLaw d n).real {x | ¬fittingFeasible d n lo hi ε x}

/-- The exact infimum appearing in the r=1 instance of the BM interface. -/
def minFittingRiskOne (d n : ℕ) (x : CoordinateSample d n) (lo hi : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ S ∈ BMRescaling.spectralBox d lo hi, t = fittingL1 S x}

/-- Exact expansion into the original real-power r=1 expression. -/
theorem minFittingRiskOne_eq_original (d n : ℕ) (x : CoordinateSample d n) (lo hi : ℝ) :
    minFittingRiskOne d n x lo hi = sInf {t : ℝ |
      ∃ S ∈ BMRescaling.spectralBox d lo hi,
        t = (1/(n:ℝ))*∑ i,
          |(BMRescaling.quadratic S (x i)-(d:ℝ))/Real.sqrt (d:ℝ)|^(1:ℝ)} := by
  simp only [minFittingRiskOne, fittingL1_eq_rpow_one]

/-- An actual fitting witness upper-bounds the literal infimum risk. -/
theorem minFittingRiskOne_le {d n : ℕ} (x : CoordinateSample d n) {lo hi : ℝ}
    {S : BMRescaling.Square d} (hS : S ∈ BMRescaling.spectralBox d lo hi) :
    minFittingRiskOne d n x lo hi ≤ fittingL1 S x := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨T, hT, rfl⟩
    unfold fittingL1 BMRescaling.empiricalL1
    positivity
  · exact ⟨S, hS, rfl⟩

/-- No attainment assumption is needed: a strict successful witness excludes
a risk larger than ε. -/
theorem minRisk_failure_subset (d n : ℕ) (lo hi ε : ℝ) :
    {x : CoordinateSample d n | ε < minFittingRiskOne d n x lo hi} ⊆
      {x | ¬fittingFeasible d n lo hi ε x} := by
  intro x hx hfit
  obtain ⟨S,hS,hfit⟩ := hfit
  exact (not_lt_of_ge ((minFittingRiskOne_le x hS).trans hfit.le)) hx

/-- A genuine r=1 infimum-risk limit follows from physical fitting failure. -/
theorem minRisk_tendsto_zero_of_fitting_failure (n : ℕ → ℕ) (lo hi ε : ℝ)
    (h : Tendsto (fun d => fittingFailureProbability d (n d) lo hi ε) atTop (nhds 0)) :
    Tendsto (fun d => (coordinateSampleLaw d (n d)).real
      {x | ε < minFittingRiskOne d (n d) x lo hi}) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _ h
  intro d
  exact measureReal_mono (minRisk_failure_subset d (n d) lo hi ε)

/-- The physical finite-sample loss is continuous for each actual matrix. -/
theorem continuous_fittingL1 {d n : ℕ} (S : BMRescaling.Square d) :
    Continuous (fun x : CoordinateSample d n => fittingL1 S x) := by
  unfold fittingL1 BMRescaling.empiricalL1 BMRescaling.fittingResidual BMRescaling.quadratic
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- Strict physical fitting failure is closed, even without any measurable
choice of a fitting matrix. -/
theorem isClosed_fitting_failure_event (d n : ℕ) (lo hi ε : ℝ) :
    IsClosed {x : CoordinateSample d n | ¬fittingFeasible d n lo hi ε x} := by
  have hclosed := isClosed_iInter (fun S : BMRescaling.Square d =>
    isClosed_iInter (fun _hS : S ∈ BMRescaling.spectralBox d lo hi =>
      isClosed_le (continuous_const : Continuous (fun _ : CoordinateSample d n => ε))
        (continuous_fittingL1 S)))
  convert hclosed using 1
  ext x
  simp only [fittingFeasible, Set.mem_iInter, Set.mem_setOf_eq, not_exists, not_and, not_lt]

/-- Physical fitting failure is an actual measurable event. -/
theorem measurableSet_fitting_failure_event (d n : ℕ) (lo hi ε : ℝ) :
    MeasurableSet {x : CoordinateSample d n | ¬fittingFeasible d n lo hi ε x} :=
  (isClosed_fitting_failure_event d n lo hi ε).measurableSet

/-- The literal original infimum risk is measurable; no attainment or
compactness premise is retained. -/
theorem measurable_minFittingRiskOne (d n : ℕ) (lo hi : ℝ) :
    Measurable (fun x : CoordinateSample d n => minFittingRiskOne d n x lo hi) := by
  letI : NormedAddCommGroup (BMRescaling.Square d) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (BMRescaling.Square d) := Matrix.normedSpace
  have hcont (S : BMRescaling.Square d) (_hS : S ∈ BMRescaling.spectralBox d lo hi) :
      Continuous (fun x : CoordinateSample d n => fittingL1 S x) := continuous_fittingL1 S
  have hbelow (x : CoordinateSample d n) : BddBelow
      ((fun S : BMRescaling.Square d => fittingL1 S x) '' BMRescaling.spectralBox d lo hi) := by
    refine ⟨0, ?_⟩
    rintro t ⟨S,hS,rfl⟩
    unfold fittingL1 BMRescaling.empiricalL1
    positivity
  have h := BMNetGroundExtension.measurable_ground_of_continuous
    (BMRescaling.spectralBox d lo hi) (fun x S => fittingL1 S x) hcont hbelow
  have heq (x : CoordinateSample d n) : minFittingRiskOne d n x lo hi =
      BMNetGroundExtension.ground (BMRescaling.spectralBox d lo hi) (fun S => fittingL1 S x) := by
    unfold minFittingRiskOne BMNetGroundExtension.ground
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor <;> rintro ⟨S,hS,ht⟩ <;> exact ⟨S,hS,ht.symm⟩
  simp_rw [heq]
  exact h

/-- The original r=1 risk tail is also measurable. -/
theorem measurableSet_minRiskOne_tail (d n : ℕ) (lo hi ε : ℝ) :
    MeasurableSet {x : CoordinateSample d n | ε < minFittingRiskOne d n x lo hi} :=
  measurableSet_lt measurable_const (measurable_minFittingRiskOne d n lo hi)

end BMBoxRiskAssembly
