import StandaloneMixedNormBound
import BMCoordinateSampleLawCore

/-!
Ordinary-coordinate bridge for the proved standalone mixed-norm theorem.
No definitions from the unavailable original Basic.lean or MixedNormAsm.lean
are assumed. The source measure, finite-vector cost, normalized quadratic
matrix and Euclidean singular-value nuclear norm are all literal below.
-/
noncomputable section
set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoidCandidate
open BMBoxRiskAssembly GaussianEllipsoidFinalPassage
open scoped BigOperators ENNReal Topology
namespace GaussianEllipsoidCoordinateBridge

/-- The literal infimal mixed norm in ordinary finite-vector coordinates. -/
def coordinateMixedNorm (η : ℝ) (d n : ℕ) (y : Fin n → ℝ) : ℝ :=
  sInf {w : ℝ | ∃ u v : Fin n → ℝ, y = u + v ∧
    w = η*Real.sqrt (d:ℝ)*(∑ i, |u i|) + (d:ℝ)*Real.sqrt (∑ i, v i^2)}

/-- Exact formula identity; no equivalence of norms or constant loss. -/
theorem coordinateMixedNorm_eq_standalone (η : ℝ) (d n : ℕ) (y : Fin n → ℝ) :
    coordinateMixedNorm η d n y = GaussianEllipsoidStandalone.mixedNorm η d n y := rfl

/-- Ordinary matrix nuclear norm defined by the singular values of the actual
Euclidean matrix operator. This is not the default entrywise matrix norm. -/
def coordinateNuclearNorm {r q : ℕ} (A : Matrix (Fin r) (Fin q) ℝ) : ℝ :=
  ∑ j : Fin q, singularValue (GaussianEllipsoid.SmallBall.matrixCLM A) j

/-- The existing column/Frobenius representation yields the genuine Euclidean
matrix operator, entry for entry and without a norm comparison. -/
theorem matrixCLM_frobeniusToMatrix {r q : ℕ} (A : FrobeniusMatrix r q) :
    GaussianEllipsoid.SmallBall.matrixCLM (frobeniusToMatrix A) = frobeniusOperator A := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin q) ℝ).toBasis.ext
  intro j
  change GaussianEllipsoid.SmallBall.matrixCLM (frobeniusToMatrix A)
      (EuclideanSpace.basisFun (Fin q) ℝ j) =
    frobeniusOperator A (EuclideanSpace.basisFun (Fin q) ℝ j)
  rw [frobeniusOperator_basis]
  ext i
  change (Matrix.toEuclideanLin (frobeniusToMatrix A)
    (EuclideanSpace.basisFun (Fin q) ℝ j)) i = A j i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    EuclideanSpace.basisFun_apply, frobeniusToMatrix]

/-- Genuine equality of spectral nuclear norms under ordinary matrix conversion. -/
theorem coordinateNuclearNorm_frobeniusToMatrix {r q : ℕ} (A : FrobeniusMatrix r q) :
    coordinateNuclearNorm (frobeniusToMatrix A) = spectralNuclearNorm A := by
  unfold coordinateNuclearNorm spectralNuclearNorm
  rw [matrixCLM_frobeniusToMatrix]

/-- The exact uncentered normalized quadratic matrix in ordinary coordinates. -/
def coordinateQuadraticSynthesis {d n : ℕ} (x : CoordinateSample d n) (y : Fin n → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a b => (1/Real.sqrt (d:ℝ)) * ∑ i, y i*x i a*x i b

/-- For zero-sum coefficients, the scalar identity centering vanishes exactly.
This identity is valid also at d=0 under Lean's total division convention. -/
theorem centeredAdjoint_coordinate_entry {d n : ℕ} (x : CoordinateSample d n)
    (y : Fin n → ℝ) (hy : (∑ i, y i) = 0) (a b : Fin d) :
    frobeniusToMatrix (GaussianEllipsoidStandalone.centeredAdjoint
      (sampleEuclideanEquiv d n x) y) a b =
      (1/Real.sqrt (d:ℝ)) * ∑ i, y i*x i a*x i b := by
  unfold GaussianEllipsoidStandalone.centeredAdjoint centeredRankOneSynthesis
  have hz : (∑ i, y i) • ContinuousLinearMap.id ℝ (Euclid d) =
      (0 : Euclid d →L[ℝ] Euclid d) := by
    ext v a
    change (∑ i, y i) * v a = 0
    rw [hy, zero_mul]
  rw [hz, sub_zero]
  change (Real.sqrt (d:ℝ))⁻¹ * operatorFrobenius
    (bilinearSynthesis y (fun i => (sampleEuclideanEquiv d n x i,
      sampleEuclideanEquiv d n x i))) b a = _
  rw [bilinearSynthesis_entry, inv_eq_one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change y i * (x i a * x i b) = y i*x i a*x i b
  ring

/-- Matrix equality, not merely an entrywise estimate. -/
theorem centeredAdjoint_coordinate_matrix {d n : ℕ} (x : CoordinateSample d n)
    (y : Fin n → ℝ) (hy : (∑ i, y i) = 0) :
    frobeniusToMatrix (GaussianEllipsoidStandalone.centeredAdjoint
      (sampleEuclideanEquiv d n x) y) = coordinateQuadraticSynthesis x y := by
  ext a b
  exact centeredAdjoint_coordinate_entry x y hy a b

/-- Exact operator identification on the zero-sum coefficient subspace. -/
theorem coordinateQuadraticSynthesis_operator {d n : ℕ} (x : CoordinateSample d n)
    (y : Fin n → ℝ) (hy : (∑ i, y i) = 0) :
    GaussianEllipsoid.SmallBall.matrixCLM (coordinateQuadraticSynthesis x y) =
      (Real.sqrt (d:ℝ))⁻¹ • centeredRankOneSynthesis y (sampleEuclideanEquiv d n x) := by
  rw [← centeredAdjoint_coordinate_matrix x y hy, matrixCLM_frobeniusToMatrix]
  exact frobeniusOperator_operatorFrobenius _

/-- Exact nuclear identification, with no unknown project norm premise. -/
theorem coordinateQuadraticSynthesis_nuclear {d n : ℕ} (x : CoordinateSample d n)
    (y : Fin n → ℝ) (hy : (∑ i, y i) = 0) :
    coordinateNuclearNorm (coordinateQuadraticSynthesis x y) =
      spectralNuclearNorm (GaussianEllipsoidStandalone.centeredAdjoint
        (sampleEuclideanEquiv d n x) y) := by
  rw [← centeredAdjoint_coordinate_matrix x y hy, coordinateNuclearNorm_frobeniusToMatrix]

/-- The already proved rowwise Gaussian equivalence targets exactly the
standalone theorem's full source law. -/
theorem coordinateSampleLaw_measurePreserving (d n : ℕ) :
    MeasurePreserving (sampleEuclideanEquiv d n) (coordinateSampleLaw d n)
      (GaussianEllipsoidStandalone.gaussianSampleLaw d n) :=
  sampleEuclideanEquiv_measurePreserving d n

/-- Exact full-sample event probability transport, even for arbitrary events. -/
theorem coordinateSampleLaw_event_probability (d n : ℕ)
    (E : Set (GaussianEllipsoidStandalone.Sample d n)) :
    (coordinateSampleLaw d n).real ((sampleEuclideanEquiv d n) ⁻¹' E) =
      (GaussianEllipsoidStandalone.gaussianSampleLaw d n).real E :=
  coordinate_event_probability d n E

/-- Unconditional ordinary-coordinate form of the mixed-norm lower bound.
The matrix inside the genuine singular-value nuclear norm is literally
(1/sqrt d) sum_i y_i x_i(a)x_i(b); only zero-sum coefficients are requested. -/
theorem unconditional_coordinate_mixed_events (n : ℕ → ℕ)
    (haspect : limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞)) :
    ∃ c : ℝ, 0 < c ∧ ∃ G : ∀ d, Set (CoordinateSample d (n d)),
      (∀ d, MeasurableSet (G d)) ∧
      (∀ d, d < 4 → G d = ∅) ∧
      limsup (fun d => (coordinateSampleLaw d (n d)).real (G d)ᶜ) atTop = 0 ∧
      ∀ d, ∀ x ∈ G d, ∀ y : Fin (n d) → ℝ, (∑ i, y i) = 0 →
        c*coordinateMixedNorm numericalEta d (n d) y ≤
          coordinateNuclearNorm (coordinateQuadraticSynthesis x y) := by
  obtain ⟨c,hc,E,hE,hEsmall,hElim,hEb⟩ :=
    GaussianEllipsoidStandalone.unconditional_full_mixed_events n haspect
  let G (d : ℕ) := (sampleEuclideanEquiv d (n d)) ⁻¹' E d
  refine ⟨c,hc,G,?_,?_,?_,?_⟩
  · intro d
    exact (hE d).preimage (sampleEuclideanEquiv d (n d)).measurable
  · intro d hd
    simp only [G, hEsmall d hd, Set.preimage_empty]
  · have heq (d : ℕ) : (coordinateSampleLaw d (n d)).real (G d)ᶜ =
        (GaussianEllipsoidStandalone.gaussianSampleLaw d (n d)).real (E d)ᶜ := by
      change (coordinateSampleLaw d (n d)).real
        ((sampleEuclideanEquiv d (n d)) ⁻¹' E d)ᶜ = _
      rw [← Set.preimage_compl, coordinateSampleLaw_event_probability]
    simp_rw [heq]
    exact hElim
  · intro d x hx y hy
    rw [coordinateMixedNorm_eq_standalone, coordinateQuadraticSynthesis_nuclear x y hy]
    exact hEb d (sampleEuclideanEquiv d (n d) x) hx y

/-- Literal every-tolerance interface with the original finite-vector norm
formula, ordinary-coordinate source law, and the actual normalized matrix. -/
theorem coordinate_mixedNormBound :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞) →
      ∀ δ > 0, ∃ η c : ℝ, ∃ G : ∀ d, Set (CoordinateSample d (n d)),
        0 < η ∧ η < 1 ∧ 0 < c ∧
        (∀ d, MeasurableSet (G d)) ∧
        limsup (fun d => (coordinateSampleLaw d (n d)).real (G d)ᶜ) atTop ≤ δ ∧
        ∀ d, ∀ x ∈ G d, ∀ y : Fin (n d) → ℝ, (∑ i, y i) = 0 →
          c*(sInf {w : ℝ | ∃ u v : Fin (n d) → ℝ, y = u+v ∧
            w = η*Real.sqrt (d:ℝ)*(∑ i, |u i|) + (d:ℝ)*Real.sqrt (∑ i, v i^2)}) ≤
            coordinateNuclearNorm (fun a b => (1/Real.sqrt (d:ℝ))*∑ i, y i*x i a*x i b) := by
  intro n _ haspect δ hδ
  obtain ⟨c,hc,G,hG,_,hlim,hb⟩ := unconditional_coordinate_mixed_events n haspect
  refine ⟨numericalEta,c,G,numerical_eta_range.1,numerical_eta_range.2.1,hc,hG,?_,hb⟩
  rw [hlim]
  exact hδ.le

end GaussianEllipsoidCoordinateBridge
