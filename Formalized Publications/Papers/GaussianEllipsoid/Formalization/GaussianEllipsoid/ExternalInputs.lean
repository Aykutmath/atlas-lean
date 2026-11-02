/-
Explicit external hypotheses for the full formalization.

Each definition below is a PROPOSITION formalizing a cited external result
used by the paper, with paper provenance. They are premises of conditional
theorems, never axioms: no `axiom` command appears anywhere. The eight
premises are: Gordon's finite min-max comparison (Theorem A), its compact
extension (Corollary 1.2), Gaussian Lipschitz concentration (Theorem 3.2),
Sudakov finite minoration, Davidson-Szarek II.13, Ambainis-Harrow-Hastings
Corollary 3 and Equation (11), and the Bandeira-Maillard approximate-fitting
theorem. The AHH and Bandeira-Maillard statements live with their use sites
(Sections 8 and 4) because their ensembles need local setup; the other five
are stated here.

Mathematical source: paper.tex, Sections 13.3 (Gordon), 5.3 (Sudakov),
7.3 (Davidson-Szarek).
-/
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory

/-- Finite minimum over a nonempty finite index type. -/
def finMin {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

/-- Finite maximum over a nonempty finite index type. -/
def finMax {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

/-- A centered real Gaussian process: Gaussian finite-dimensional laws,
integrable marginals, zero mean. Covariances are expressed through
Bochner integrals at each use site. -/
def IsCenteredGaussianProcess {Ω T : Type*} [MeasurableSpace Ω]
    (X : T → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsGaussianProcess X P ∧
    (∀ t, Integrable (X t) P) ∧ ∀ t, ∫ ω, X t ω ∂P = 0

/-- Gordon 1988, Theorem A: finite Gaussian min-max comparison.
If the X-increments dominate on same-row pairs and are dominated on
cross-row pairs, then E min max X <= E min max Y.
Used in paper.tex Section 13.3 (lem:infeasibility_above:gaussian_escape). -/
def gordonFiniteMinMax : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : I × J → Ω → ℝ),
    IsCenteredGaussianProcess X P → IsCenteredGaussianProcess Y P →
    (∀ p q, Integrable (fun ω => (X p ω - X q ω) ^ 2) P) →
    (∀ p q, Integrable (fun ω => (Y p ω - Y q ω) ^ 2) P) →
    (∀ i j k, ∫ ω, (X (i, j) ω - X (i, k) ω) ^ 2 ∂P ≤
      ∫ ω, (Y (i, j) ω - Y (i, k) ω) ^ 2 ∂P) →
    (∀ i l j k, i ≠ l →
      ∫ ω, (Y (i, j) ω - Y (l, k) ω) ^ 2 ∂P ≤
      ∫ ω, (X (i, j) ω - X (l, k) ω) ^ 2 ∂P) →
    Integrable (fun ω => finMin (fun i => finMax (fun j => X (i, j) ω))) P →
    Integrable (fun ω => finMin (fun i => finMax (fun j => Y (i, j) ω))) P →
    ∫ ω, finMin (fun i => finMax (fun j => X (i, j) ω)) ∂P ≤
      ∫ ω, finMin (fun i => finMax (fun j => Y (i, j) ω)) ∂P

/-- Min-max value over compact index sets, via images of the full sets.
For continuous paths on nonempty compacta these are the true extrema. -/
def compactMinMax {K L Ω : Type*} [TopologicalSpace K] [TopologicalSpace L]
    [CompactSpace K] [CompactSpace L] [Nonempty K] [Nonempty L]
    (X : K × L → Ω → ℝ) (ω : Ω) : ℝ :=
  sInf ((fun k => sSup ((fun l => X (k, l) ω) '' Set.univ)) '' Set.univ)

/-- Gordon 1988, Corollary 1.2: the finite comparison extends to compact
index sets for processes with almost surely continuous paths.
Used in paper.tex Section 13.3 to pass from finite nets to
P_p x S^{r-1}. -/
def gordonCompactExtension : Prop :=
  ∀ (K L : Type) [TopologicalSpace K] [TopologicalSpace L]
    [CompactSpace K] [CompactSpace L] [Nonempty K] [Nonempty L]
    [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : K × L → Ω → ℝ),
    IsCenteredGaussianProcess X P → IsCenteredGaussianProcess Y P →
    (∀ᵐ ω ∂P, Continuous (fun p : K × L => X p ω)) →
    (∀ᵐ ω ∂P, Continuous (fun p : K × L => Y p ω)) →
    (∀ p q, Integrable (fun ω => (X p ω - X q ω) ^ 2) P) →
    (∀ p q, Integrable (fun ω => (Y p ω - Y q ω) ^ 2) P) →
    (∀ k l m, ∫ ω, (X (k, l) ω - X (k, m) ω) ^ 2 ∂P ≤
      ∫ ω, (Y (k, l) ω - Y (k, m) ω) ^ 2 ∂P) →
    (∀ k k' l m, k ≠ k' →
      ∫ ω, (Y (k, l) ω - Y (k', m) ω) ^ 2 ∂P ≤
      ∫ ω, (X (k, l) ω - X (k', m) ω) ^ 2 ∂P) →
    Measurable (compactMinMax X) → Measurable (compactMinMax Y) →
    Integrable (compactMinMax X) P → Integrable (compactMinMax Y) P →
    ∫ ω, compactMinMax X ω ∂P ≤ ∫ ω, compactMinMax Y ω ∂P

/-- One-Lipschitz against the explicit Euclidean length, avoiding a
metric-space instance on coordinate functions. -/
def euclideanLipschitzOne {N : ℕ} (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ Real.sqrt (∑ i, (x i - y i) ^ 2)

/-- Gordon 1988, Theorem 3.2: Gaussian concentration for Lipschitz
functions of a standard Gaussian vector.
Used in paper.tex Section 13.3 for the escape tail. -/
def gordonGaussianConcentration : Prop :=
  ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → (Fin N → ℝ)),
    P.map X = Measure.pi (fun _ : Fin N => gaussianReal 0 1) →
    ∀ (f : (Fin N → ℝ) → ℝ),
      euclideanLipschitzOne f → Integrable (fun ω => f (X ω)) P →
      ∀ t : ℝ, 0 < t →
        P {ω | f (X ω) < (∫ ω, f (X ω) ∂P) - t} ≤
          ENNReal.ofReal (Real.exp (-t ^ 2 / 2))

/-- Sudakov minoration in finite-set form (Fernique 1974, Section 2.1):
M points with pairwise canonical distance at least epsilon have
expected supremum at least c epsilon sqrt(log M).
Used in paper.tex Section 5.3 (lem:det-nuclear-cover). -/
def sudakovFiniteMinoration : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (M : ℕ) (hM : 0 < M) (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin M → Ω → ℝ)
      (ε : ℝ) (_hε : 0 < ε),
      IsCenteredGaussianProcess X P →
      (∀ i j, Integrable (fun ω => (X i ω - X j ω) ^ 2) P) →
      (∀ i j, i ≠ j → ε ^ 2 ≤ ∫ ω, (X i ω - X j ω) ^ 2 ∂P) →
      Integrable (fun ω => @finMax (Fin M) _ ⟨⟨0, hM⟩⟩ (fun i => X i ω)) P →
      c * ε * Real.sqrt (Real.log (M : ℝ)) ≤
        ∫ ω, @finMax (Fin M) _ ⟨⟨0, hM⟩⟩ (fun i => X i ω) ∂P

/-- Squared smallest singular value: infimum of ||M v||^2 over the unit
sphere, with the Euclidean length written explicitly. -/
def sqMinSingularValue {h s : ℕ} (M : Matrix (Fin h) (Fin s) ℝ) : ℝ :=
  sInf ((fun v : Fin s → ℝ =>
    dotProduct (Matrix.mulVec M v) (Matrix.mulVec M v)) '' {v | dotProduct v v = 1})

/-- Smallest singular value. -/
def minSingularValue {h s : ℕ} (M : Matrix (Fin h) (Fin s) ℝ) : ℝ :=
  Real.sqrt (sqMinSingularValue M)

/-- Davidson-Szarek 2001, Theorem II.13: smallest singular value of a
tall Gaussian matrix. Used in paper.tex Section 7.3
(record-lemma-3-2). -/
def davidsonSzarekMinSingular : Prop :=
  ∀ (h s : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (M : Ω → Matrix (Fin h) (Fin s) ℝ),
    (∀ i j, MeasurePreserving (fun ω => M ω i j) P (gaussianReal 0 1)) →
    iIndepFun (fun p : Fin h × Fin s => fun ω => M ω p.1 p.2) P →
    ∀ t : ℝ, 0 < t →
      P {ω | minSingularValue (M ω) ≤
          Real.sqrt (h : ℝ) - Real.sqrt (s : ℝ) - t} ≤
        ENNReal.ofReal (Real.exp (-t ^ 2 / 2))

end GaussianEllipsoid
