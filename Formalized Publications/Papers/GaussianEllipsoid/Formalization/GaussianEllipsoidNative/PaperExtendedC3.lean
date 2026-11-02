import PaperIsonormalCavity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth PaperGibbsThird PaperRowSecondStein
open scoped BigOperators BoundedContinuousFunction InnerProductSpace ENNReal
namespace GaussianEllipsoid.PaperExtendedC3
open PaperCavityProduct

/-- Explicit extended-supremum representation of the paper's derivative norm.
It is allowed to be infinity and is not asserted to be a finite real norm. -/
def derivativeSup (ell : ℝ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ⨆ t : ℝ, ENNReal.ofReal |iteratedDeriv j ell t|

lemma derivative_le_sup (ell : ℝ → ℝ) (j : ℕ) (t : ℝ) :
    ENNReal.ofReal |iteratedDeriv j ell t| ≤ derivativeSup ell j :=
  le_iSup (fun t : ℝ => ENNReal.ofReal |iteratedDeriv j ell t|) t

lemma derivative_le_toReal (ell : ℝ → ℝ) (j : ℕ)
    (hj : derivativeSup ell j ≠ ⊤) (t : ℝ) :
    |iteratedDeriv j ell t| ≤ (derivativeSup ell j).toReal := by
  have h := ENNReal.toReal_mono hj (derivative_le_sup ell j t)
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h

def boundedDerivative (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell) (j : ℕ)
    (hj3 : j ≤ 3) (hj : derivativeSup ell j ≠ ⊤) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (iteratedDeriv j ell)
    (hell.continuous_iteratedDeriv j (by exact_mod_cast hj3))
    (derivativeSup ell j).toReal (fun t => by
      simpa only [Real.norm_eq_abs] using derivative_le_toReal ell j hj t)

@[simp] lemma boundedDerivative_apply (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell)
    (j : ℕ) (hj3 : j ≤ 3) (hj : derivativeSup ell j ≠ ⊤) (t : ℝ) :
    boundedDerivative ell hell j hj3 hj t = iteratedDeriv j ell t := rfl

lemma boundedDerivative_norm (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell)
    (j : ℕ) (hj3 : j ≤ 3) (hj : derivativeSup ell j ≠ ⊤) :
    ‖boundedDerivative ell hell j hj3 hj‖ = (derivativeSup ell j).toReal := by
  have he : ENNReal.ofReal ‖boundedDerivative ell hell j hj3 hj‖ = derivativeSup ell j := by
    simpa only [ofReal_norm, derivativeSup, Real.enorm_eq_ofReal_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), boundedDerivative_apply] using
      (boundedDerivative ell hell j hj3 hj).enorm_eq_iSup_enorm
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using ht

def boundedLoss (ell : ℝ → ℝ) (hell : Continuous ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup ell hell 1 (fun t => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hunit t).1] using (hunit t).2)

/-- Every field of the C3 Gibbs package is constructed from actual C3 regularity
and finite extended derivative suprema. No analytic Data3 package is assumed. -/
def data3 {κ : Type*} [Fintype κ] [Nonempty κ] (β : ℝ) (hβ : 0 < β)
    (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell) (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (h1 : derivativeSup ell 1 ≠ ⊤) (h2 : derivativeSup ell 2 ≠ ⊤)
    (h3 : derivativeSup ell 3 ≠ ⊤) : Data3 κ where
  weight := fun _ => (Fintype.card κ : ℝ)⁻¹
  weight_nonneg := fun _ => by positivity
  weight_sum := by
    have hc : (Fintype.card κ : ℝ) ≠ 0 := by positivity
    simp [hc]
  potential := boundedLoss ell hell.continuous hunit
  potentialDeriv := boundedDerivative ell hell 1 (by omega) h1
  hasDeriv t := by
    change HasDerivAt ell (iteratedDeriv 1 ell t) t
    simpa only [iteratedDeriv_one] using (hell.differentiable (by norm_num) t).hasDerivAt
  beta := β
  beta_nonneg := hβ.le
  potentialSecond := boundedDerivative ell hell 2 (by omega) h2
  hasDeriv_second t := by
    change HasDerivAt (iteratedDeriv 1 ell) (iteratedDeriv 2 ell t) t
    simpa only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ] using
      (hell.differentiable_iteratedDeriv 1 (by norm_num) t).hasDerivAt
  potentialThird := boundedDerivative ell hell 3 (by omega) h3
  hasDeriv_third t := by
    change HasDerivAt (iteratedDeriv 2 ell) (iteratedDeriv 3 ell t) t
    simpa only [show 3 = 2 + 1 from rfl, iteratedDeriv_succ] using
      (hell.differentiable_iteratedDeriv 2 (by norm_num) t).hasDerivAt

#print axioms data3
#print axioms boundedDerivative_norm

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

def cavityGap {d n : ℕ} (β : ℝ) (ell : ℝ → ℝ)
    (R : κ → Square d) (c : Fin n → κ → ℝ) : ℝ :=
  |(∫ x : Fin n → Vector d, paperFreeEnergy β ell
      (fun i a => (quadratic (R a) (x i)-Matrix.trace (R a))/Real.sqrt 2+c i a)
        ∂Measure.pi (fun _ : Fin n => gaussianVectorLaw d))-
    ∫ z : Fin n → (Fin (d*d) → ℝ), paperFreeEnergy β ell
      (fun i a => UCNormalizedRows.gaussianRow (R a) (z i)+c i a)
        ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))|

/-- The exact finite-constant expression, represented in extended nonnegative reals. -/
def extendedBound (β τ : ℝ) (ell : ℝ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*β)*τ) *
    (derivativeSup ell 3 + ENNReal.ofReal β * derivativeSup ell 1 * derivativeSup ell 2 +
      (ENNReal.ofReal β)^2 * (derivativeSup ell 1)^3)

lemma finite_bound_representation (β τ : ℝ) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (ell : ℝ → ℝ) (h1 : derivativeSup ell 1 ≠ ⊤)
    (h2 : derivativeSup ell 2 ≠ ⊤) (h3 : derivativeSup ell 3 ≠ ⊤) :
    extendedBound β τ ell = ENNReal.ofReal
      ((3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*β)*τ*
        ((derivativeSup ell 3).toReal + β*(derivativeSup ell 1).toReal*(derivativeSup ell 2).toReal +
          β^2*(derivativeSup ell 1).toReal^3)) := by
  symm
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [extendedBound, ENNReal.ofReal_mul hβ, ENNReal.ofReal_mul (by positivity :
      0 ≤ β * (derivativeSup ell 1).toReal), ENNReal.ofReal_mul (sq_nonneg β),
    ENNReal.ofReal_pow hβ, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal h1, ENNReal.ofReal_toReal h2, ENNReal.ofReal_toReal h3]

/-- A real finite-supremum version, constructed from ell itself. -/
theorem comparison_finite_suprema {d n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (h1 : derivativeSup ell 1 ≠ ⊤) (h2 : derivativeSup ell 2 ≠ ⊤)
    (h3 : derivativeSup ell 3 ≠ ⊤)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose = R a)
    {τ : ℝ} (hop : ∀ a, matrixOpNorm (R a) ≤ τ)
    (hfrob : ∀ a, frobeniusNorm (R a) ≤ 1) (c : Fin n → κ → ℝ) :
    cavityGap β ell R c ≤
      (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*β)*τ*
        ((derivativeSup ell 3).toReal + β*(derivativeSup ell 1).toReal*(derivativeSup ell 2).toReal +
          β^2*(derivativeSup ell 1).toReal^3) := by
  let D : Data3 κ := data3 β hβ ell hell hunit h1 h2 h3
  have h := PaperCavityProduct.paper_cavity_comparison_finite_derivatives hn D hβ hunit R hR hop hfrob c
  simpa only [cavityGap, D, data3, boundedLoss, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    boundedDerivative_norm] using h

lemma sup_one_zero_implies_const (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell)
    (h1 : derivativeSup ell 1 = 0) : ell = fun _ => ell 0 := by
  have hd (t : ℝ) : deriv ell t = 0 := by
    have hh := derivative_le_sup ell 1 t
    rw [h1, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hh
    exact abs_eq_zero.mp (le_antisymm (by simpa only [iteratedDeriv_one] using hh) (abs_nonneg _))
  funext t
  exact is_const_of_deriv_eq_zero (hell.differentiable (by norm_num)) hd t 0

lemma derivativeSup_const (v : ℝ) (j : ℕ) (hj : 0 < j) :
    derivativeSup (fun _ : ℝ => v) j = 0 := by
  simp [derivativeSup, iteratedDeriv_const, hj.ne']

lemma cavityGap_zero_matrices {d n : ℕ} (β : ℝ) (ell : ℝ → ℝ)
    (R : κ → Square d) (hR : ∀ a, R a = 0) (c : Fin n → κ → ℝ) :
    cavityGap β ell R c = 0 := by
  simp [cavityGap, hR, quadratic_eq_sum, UCNormalizedRows.gaussianRow]

/-- Full C3 comparison under the explicit extended-supremum convention.
No finite derivative-supremum premise is made. In particular all zero-times-infinity
cases are resolved from the observables, rather than discarded algebraically. -/
theorem paper_cavity_comparison_extended {d n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose = R a)
    {τ : ℝ} (hop : ∀ a, matrixOpNorm (R a) ≤ τ)
    (hfrob : ∀ a, frobeniusNorm (R a) ≤ 1) (c : Fin n → κ → ℝ) :
    ENNReal.ofReal (cavityGap β ell R c) ≤ extendedBound β τ ell := by
  have hτ : 0 ≤ τ := (matrixOpNorm_nonneg (R (Classical.choice inferInstance))).trans
    (hop (Classical.choice inferInstance))
  by_cases ht : τ = 0
  · have hzero (a : κ) : R a = 0 := (matrixOpNorm_eq_zero_iff _).mp
      (le_antisymm (ht ▸ hop a) (matrixOpNorm_nonneg _))
    rw [cavityGap_zero_matrices β ell R hzero c]
    simp
  have hpref : ENNReal.ofReal ((3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*β)*τ) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (mul_pos (by positivity) (Real.exp_pos _)) (lt_of_le_of_ne hτ (Ne.symm ht))
  by_cases h1zero : derivativeSup ell 1 = 0
  · have hc := sup_one_zero_implies_const ell hell h1zero
    have hfinite (j : ℕ) (hj : 0 < j) : derivativeSup ell j ≠ ⊤ := by
      rw [hc, derivativeSup_const _ j hj]
      simp
    rw [finite_bound_representation β τ hβ.le hτ ell (hfinite 1 (by omega))
      (hfinite 2 (by omega)) (hfinite 3 (by omega))]
    exact ENNReal.ofReal_le_ofReal (comparison_finite_suprema hn β hβ ell hell hunit
      (hfinite 1 (by omega)) (hfinite 2 (by omega)) (hfinite 3 (by omega)) R hR hop hfrob c)
  by_cases h1 : derivativeSup ell 1 = ⊤
  · have hb : ENNReal.ofReal β ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hβ)
    simp [extendedBound, h1, hpref, hb]
  by_cases h2 : derivativeSup ell 2 = ⊤
  · have hb : ENNReal.ofReal β ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hβ)
    simp [extendedBound, h2, hpref, hb, h1zero]
  by_cases h3 : derivativeSup ell 3 = ⊤
  · simp [extendedBound, h3, hpref]
  rw [finite_bound_representation β τ hβ.le hτ ell h1 h2 h3]
  exact ENNReal.ofReal_le_ofReal (comparison_finite_suprema hn β hβ ell hell hunit h1 h2 h3 R hR hop hfrob c)

#print axioms comparison_finite_suprema
#print axioms paper_cavity_comparison_extended


/-- Finite extended norms recover exactly the real-valued comparison, including
all constants. This is the explicit representation bridge, not a change to ell. -/
theorem finite_real_inequality_iff (β τ gap : ℝ) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (ell : ℝ → ℝ) (h1 : derivativeSup ell 1 ≠ ⊤)
    (h2 : derivativeSup ell 2 ≠ ⊤) (h3 : derivativeSup ell 3 ≠ ⊤) :
    ENNReal.ofReal gap ≤ extendedBound β τ ell ↔
    gap ≤ (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*β)*τ*
      ((derivativeSup ell 3).toReal + β*(derivativeSup ell 1).toReal*(derivativeSup ell 2).toReal +
        β^2*(derivativeSup ell 1).toReal^3) := by
  rw [finite_bound_representation β τ hβ hτ ell h1 h2 h3]
  exact ENNReal.ofReal_le_ofReal_iff (by positivity)

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

/-- Gaussian law transport requires only continuity of the original ell. It
therefore applies unchanged when some derivative suprema are infinite. -/
theorem gaussian_freeEnergy_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ}
    (β : ℝ) (ell : ℝ → ℝ) (hell : Continuous ell)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose = R a)
    (c : Fin n → κ → ℝ) (G : Fin n → Ω → SymFrob d)
    (hG : ∀ i, Measurable (G i)) (hind : iIndepFun G μ)
    (hiso : ∀ i, IsIsonormalSymLaw d (μ.map (G i))) :
    (∫ z : Fin n → (Fin (d*d) → ℝ), paperFreeEnergy β ell
      (fun i a => UCNormalizedRows.gaussianRow (R a) (z i)+c i a)
      ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))) =
    ∫ ω, paperFreeEnergy β ell
      (fun i a => ⟪ofMatrix (R a) (hR a), G i ω⟫_ℝ+c i a) ∂μ := by
  let F := fun x : Fin n → SymFrob d => paperFreeEnergy β ell
    (fun i a => ⟪ofMatrix (R a) (hR a), x i⟫_ℝ+c i a)
  have hF : Measurable F := by
    unfold F paperFreeEnergy
    fun_prop
  have hp : MeasurePreserving (fun ω => fun i => G i ω) μ
      (Measure.pi (fun _ : Fin n => stdGaussian (SymFrob d))) :=
    ⟨measurable_pi_iff.mpr hG, iid_isonormal_symmetric_rows_law μ d n G hG hind hiso⟩
  have hc := measurePreserving_pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))
    (fun _ : Fin n => stdGaussian (SymFrob d)) (fun _ => symmetrizedFullEntry_preserving d)
  have hleft := integral_comp_preserving hc hF.aestronglyMeasurable
  have hright := integral_comp_preserving hp hF.aestronglyMeasurable
  rw [← hright] at hleft
  simpa only [F, symmetrizedFullEntry_inner, matrix_ofMatrix] using hleft

/-- Paper-facing C3 endpoint for arbitrary iid isonormal symmetric Gaussian rows.
The source's derivative norms are represented by explicit ENNReal suprema. There
is no assumption that any of those suprema is finite. -/
theorem paper_cavity_comparison_extended_isonormal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose = R a)
    {τ : ℝ} (hop : ∀ a, matrixOpNorm (R a) ≤ τ)
    (hfrob : ∀ a, frobeniusNorm (R a) ≤ 1) (c : Fin n → κ → ℝ)
    (G : Fin n → Ω → SymFrob d) (hG : ∀ i, Measurable (G i))
    (hind : iIndepFun G μ) (hiso : ∀ i, IsIsonormalSymLaw d (μ.map (G i))) :
    ENNReal.ofReal |(∫ x : Fin n → Vector d, paperFreeEnergy β ell
      (fun i a => (quadratic (R a) (x i)-Matrix.trace (R a))/Real.sqrt 2+c i a)
        ∂Measure.pi (fun _ : Fin n => gaussianVectorLaw d))-
      ∫ ω, paperFreeEnergy β ell
        (fun i a => ⟪ofMatrix (R a) (hR a), G i ω⟫_ℝ+c i a) ∂μ| ≤
    ENNReal.ofReal ((3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*β)*τ) *
      (derivativeSup ell 3 + ENNReal.ofReal β * derivativeSup ell 1 * derivativeSup ell 2 +
        (ENNReal.ofReal β)^2 * (derivativeSup ell 1)^3) := by
  rw [← gaussian_freeEnergy_integral_eq μ β ell hell.continuous R hR c G hG hind hiso]
  exact paper_cavity_comparison_extended hn β hβ ell hell hunit R hR hop hfrob c

#print axioms finite_real_inequality_iff
#print axioms gaussian_freeEnergy_integral_eq
#print axioms paper_cavity_comparison_extended_isonormal


/-- Explicit finite-norm corollary on the same arbitrary iid isonormal model. -/
theorem paper_cavity_comparison_finite_suprema_isonormal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell)
    (hunit : ∀ t, 0 ≤ ell t ∧ ell t ≤ 1)
    (h1 : derivativeSup ell 1 ≠ ⊤) (h2 : derivativeSup ell 2 ≠ ⊤)
    (h3 : derivativeSup ell 3 ≠ ⊤)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose = R a)
    {τ : ℝ} (hop : ∀ a, matrixOpNorm (R a) ≤ τ)
    (hfrob : ∀ a, frobeniusNorm (R a) ≤ 1) (c : Fin n → κ → ℝ)
    (G : Fin n → Ω → SymFrob d) (hG : ∀ i, Measurable (G i))
    (hind : iIndepFun G μ) (hiso : ∀ i, IsIsonormalSymLaw d (μ.map (G i))) :
    |(∫ x : Fin n → Vector d, paperFreeEnergy β ell
      (fun i a => (quadratic (R a) (x i)-Matrix.trace (R a))/Real.sqrt 2+c i a)
        ∂Measure.pi (fun _ : Fin n => gaussianVectorLaw d))-
      ∫ ω, paperFreeEnergy β ell
        (fun i a => ⟪ofMatrix (R a) (hR a), G i ω⟫_ℝ+c i a) ∂μ| ≤
    (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*β)*τ*
      ((derivativeSup ell 3).toReal + β*(derivativeSup ell 1).toReal*(derivativeSup ell 2).toReal +
        β^2*(derivativeSup ell 1).toReal^3) := by
  have hτ : 0 ≤ τ := (matrixOpNorm_nonneg (R (Classical.choice inferInstance))).trans
    (hop (Classical.choice inferInstance))
  apply (finite_real_inequality_iff β τ _ hβ.le hτ ell h1 h2 h3).mp
  exact paper_cavity_comparison_extended_isonormal μ hn β hβ ell hell hunit R hR hop hfrob c G hG hind hiso

/-- Equality between the explicit extended supremum and the genuine bounded
continuous-function norm; finiteness is used exactly at this representation step. -/
lemma derivativeSup_eq_ofReal_norm (ell : ℝ → ℝ) (hell : ContDiff ℝ 3 ell)
    (j : ℕ) (hj3 : j ≤ 3) (hj : derivativeSup ell j ≠ ⊤) :
    derivativeSup ell j = ENNReal.ofReal ‖boundedDerivative ell hell j hj3 hj‖ := by
  rw [boundedDerivative_norm, ENNReal.ofReal_toReal hj]

#print axioms derivativeSup
#print axioms derivative_le_sup
#print axioms derivative_le_toReal
#print axioms boundedDerivative
#print axioms boundedDerivative_apply
#print axioms boundedLoss
#print axioms cavityGap
#print axioms extendedBound
#print axioms finite_bound_representation
#print axioms sup_one_zero_implies_const
#print axioms derivativeSup_const
#print axioms cavityGap_zero_matrices
#print axioms paper_cavity_comparison_finite_suprema_isonormal
#print axioms derivativeSup_eq_ofReal_norm

end GaussianEllipsoid.PaperExtendedC3
