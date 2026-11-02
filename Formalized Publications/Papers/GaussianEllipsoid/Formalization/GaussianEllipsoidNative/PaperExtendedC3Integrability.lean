import PaperExtendedC3

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth PaperGibbsThird PaperRowSecondStein
open scoped BigOperators BoundedContinuousFunction InnerProductSpace ENNReal
namespace GaussianEllipsoid.PaperExtendedC3
open PaperCavityProduct
variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Uniform unit-interval bound on the literal paper free energy. No derivative
boundedness or smoothness is needed for this pointwise fact. -/
theorem paperFreeEnergy_mem_unit_interval {n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1) (X : Fin n → κ → ℝ) :
    0 ≤ paperFreeEnergy β ell X ∧ paperFreeEnergy β ell X ≤ 1 := by
  simpa only [paperFreeEnergy, FiniteFreeEnergy.freeEnergy,
    FiniteFreeEnergy.partitionAverage, FiniteFreeEnergy.partitionSum,
    FiniteFreeEnergy.totalLoss, div_eq_mul_inv, mul_comm] using
    FiniteFreeEnergy.freeEnergy_of_bounded_rows_mem_unit_interval β n hβ hn
      (fun i a => ell (X i a)) (fun i a => hunit (X i a))

/-- Actual integrability of the paper free energy for every measurable row map
on a finite measure space, including losses with infinite derivative suprema. -/
theorem paperFreeEnergy_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ) (hell : Continuous ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (X : Ω → Fin n → κ → ℝ) (hX : Measurable X) :
    Integrable (fun ω => paperFreeEnergy β ell (X ω)) μ := by
  have hm : Measurable (fun ω => paperFreeEnergy β ell (X ω)) := by
    unfold paperFreeEnergy
    fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  have h := paperFreeEnergy_mem_unit_interval hn β hβ ell hunit (X ω)
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

/-- The rank-one expectation in the unrestricted extended endpoint is genuine. -/
theorem rank_one_freeEnergy_integrable {d n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ) (hell : Continuous ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (R : κ → Square d) (c : Fin n → κ → ℝ) :
    Integrable (fun x : Fin n → Vector d => paperFreeEnergy β ell
      (fun i a => (quadratic (R a) (x i)-Matrix.trace (R a))/Real.sqrt 2+c i a))
      (Measure.pi (fun _ : Fin n => gaussianVectorLaw d)) := by
  apply paperFreeEnergy_integrable _ hn β hβ ell hell hunit
  simp_rw [quadratic_eq_sum]
  fun_prop

/-- The full-entry Gaussian expectation is genuine even for infinite norms. -/
theorem canonical_freeEnergy_integrable {d n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ) (hell : Continuous ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (R : κ → Square d) (c : Fin n → κ → ℝ) :
    Integrable (fun z : Fin n → (Fin (d*d) → ℝ) => paperFreeEnergy β ell
      (fun i a => UCNormalizedRows.gaussianRow (R a) (z i)+c i a))
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))) := by
  apply paperFreeEnergy_integrable _ hn β hβ ell hell hunit
  unfold UCNormalizedRows.gaussianRow
  fun_prop

open GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open PaperIsonormal BMGordon
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) :=
  Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) :=
  Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) :=
  Submodule.innerProductSpace (symmetricFrobenius p)

/-- The arbitrary isonormal expectation is genuine. Only measurable rows and
finite total measure are needed; neither Gaussianity nor derivative bounds enter. -/
theorem isonormal_freeEnergy_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {d n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ) (hell : Continuous ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose = R a)
    (c : Fin n → κ → ℝ) (G : Fin n → Ω → SymFrob d)
    (hG : ∀ i, Measurable (G i)) :
    Integrable (fun ω => paperFreeEnergy β ell
      (fun i a => ⟪ofMatrix (R a) (hR a), G i ω⟫_ℝ+c i a)) μ := by
  apply paperFreeEnergy_integrable μ hn β hβ ell hell hunit
  fun_prop

/-- Complete source-facing endpoint: both expectations are proved integrable,
then compared with explicit extended derivative suprema and no finiteness premise. -/
theorem paper_cavity_comparison_extended_with_integrability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose = R a)
    {τ : ℝ} (hop : ∀ a, matrixOpNorm (R a) ≤ τ)
    (hfrob : ∀ a, frobeniusNorm (R a) ≤ 1) (c : Fin n → κ → ℝ)
    (G : Fin n → Ω → SymFrob d) (hG : ∀ i, Measurable (G i))
    (hind : iIndepFun G μ) (hiso : ∀ i, IsIsonormalSymLaw d (μ.map (G i))) :
    let FZ := fun x : Fin n → Vector d => paperFreeEnergy β ell
      (fun i a => (quadratic (R a) (x i)-Matrix.trace (R a))/Real.sqrt 2+c i a)
    let FG := fun ω => paperFreeEnergy β ell
      (fun i a => ⟪ofMatrix (R a) (hR a), G i ω⟫_ℝ+c i a)
    Integrable FZ (Measure.pi (fun _ : Fin n => gaussianVectorLaw d)) ∧
    Integrable FG μ ∧
    ENNReal.ofReal |(∫ x, FZ x ∂Measure.pi (fun _ : Fin n => gaussianVectorLaw d))-
      ∫ ω, FG ω ∂μ| ≤
    ENNReal.ofReal ((3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*β)*τ) *
      (derivativeSup ell 3 + ENNReal.ofReal β * derivativeSup ell 1 * derivativeSup ell 2 +
        (ENNReal.ofReal β)^2 * (derivativeSup ell 1)^3) := by
  exact ⟨rank_one_freeEnergy_integrable hn β hβ ell hell.continuous hunit R c,
    isonormal_freeEnergy_integrable μ hn β hβ ell hell.continuous hunit R hR c G hG,
    paper_cavity_comparison_extended_isonormal μ hn β hβ ell hell hunit R hR hop hfrob c G hG hind hiso⟩

#print axioms paperFreeEnergy_mem_unit_interval
#print axioms paperFreeEnergy_integrable
#print axioms rank_one_freeEnergy_integrable
#print axioms canonical_freeEnergy_integrable
#print axioms isonormal_freeEnergy_integrable
#print axioms paper_cavity_comparison_extended_with_integrability
end GaussianEllipsoid.PaperExtendedC3
