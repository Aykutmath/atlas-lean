import BMGordonExpectations
import CanonicalSymGaussian
import PaperCavitySource

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth PaperGibbsThird PaperRowSecondStein
open GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open scoped BigOperators BoundedContinuousFunction InnerProductSpace
namespace GaussianEllipsoid.PaperIsonormalCavity
open PaperIsonormal PaperCavityProduct
open BMGordon
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)
variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

lemma freeEnergy_rows_measurable {d n : ℕ} (D : Data3 κ)
    (R : κ → Square d) (hR : ∀ a,(R a).transpose=R a) (c : Fin n → κ → ℝ) :
    Measurable (fun G : Fin n → SymFrob d => paperFreeEnergy D.beta D.potential
      (fun i a => ⟪ofMatrix (R a) (hR a),G i⟫_ℝ+c i a)) := by
  unfold paperFreeEnergy
  fun_prop

/-- Actual arbitrary iid isonormal rows and the canonical Gaussian row model
have equal free-energy expectations, for the literal uniform finite prior. -/
theorem gaussian_freeEnergy_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ}
    (D : Data3 κ) (R : κ → Square d) (hR : ∀ a,(R a).transpose=R a)
    (c : Fin n → κ → ℝ) (G : Fin n → Ω → SymFrob d)
    (hG : ∀ i,Measurable (G i)) (hind : iIndepFun G μ)
    (hiso : ∀ i,IsIsonormalSymLaw d (μ.map (G i))) :
    (∫ z : Fin n → (Fin (d*d) → ℝ), paperFreeEnergy D.beta D.potential
      (fun i a => UCNormalizedRows.gaussianRow (R a) (z i)+c i a)
      ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))) =
    ∫ ω, paperFreeEnergy D.beta D.potential
      (fun i a => ⟪ofMatrix (R a) (hR a),G i ω⟫_ℝ+c i a) ∂μ := by
  let F := fun x : Fin n → SymFrob d => paperFreeEnergy D.beta D.potential
    (fun i a => ⟪ofMatrix (R a) (hR a),x i⟫_ℝ+c i a)
  have hF : Measurable F := freeEnergy_rows_measurable D R hR c
  have hp : MeasurePreserving (fun ω => fun i => G i ω) μ
      (Measure.pi (fun _ : Fin n => stdGaussian (SymFrob d))) :=
    ⟨measurable_pi_iff.mpr hG,iid_isonormal_symmetric_rows_law μ d n G hG hind hiso⟩
  have hc := measurePreserving_pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))
    (fun _ : Fin n => stdGaussian (SymFrob d)) (fun _ => symmetrizedFullEntry_preserving d)
  have hleft := integral_comp_preserving hc hF.aestronglyMeasurable
  have hright := integral_comp_preserving hp hF.aestronglyMeasurable
  rw [← hright] at hleft
  simpa only [F,symmetrizedFullEntry_inner,matrix_ofMatrix] using hleft

/-- The finite-L_j C3 comparison with arbitrary independent centered isonormal
symmetric Gaussian rows on any probability space. All source constants and
normalizations are unchanged. -/
theorem paper_cavity_comparison_finite_derivatives {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} (hn : 0<n)
    (D : Data3 κ) (hβ : 0<D.beta) (hunit : ∀ t,0≤D.potential t ∧ D.potential t≤1)
    (R : κ → Square d) (hR : ∀ a,(R a).transpose=R a)
    {τ : ℝ} (hop : ∀ a,matrixOpNorm (R a)≤τ) (hfrob : ∀ a,frobeniusNorm (R a)≤1)
    (c : Fin n → κ → ℝ) (G : Fin n → Ω → SymFrob d)
    (hG : ∀ i,Measurable (G i)) (hind : iIndepFun G μ)
    (hiso : ∀ i,IsIsonormalSymLaw d (μ.map (G i))) :
    |(∫ x : Fin n → Vector d, paperFreeEnergy D.beta D.potential
        (fun i a => (quadratic (R a) (x i)-Matrix.trace (R a))/Real.sqrt 2+c i a)
          ∂Measure.pi (fun _ : Fin n => gaussianVectorLaw d))-
      ∫ ω, paperFreeEnergy D.beta D.potential
        (fun i a => ⟪ofMatrix (R a) (hR a),G i ω⟫_ℝ+c i a) ∂μ| ≤
      (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*D.beta)*τ*
        (‖D.potentialThird‖+D.beta*‖D.potentialDeriv‖*‖D.potentialSecond‖+
          D.beta^2*‖D.potentialDeriv‖^3) := by
  rw [← gaussian_freeEnergy_integral_eq μ D R hR c G hG hind hiso]
  exact PaperCavityProduct.paper_cavity_comparison_finite_derivatives hn D hβ hunit R hR hop hfrob c

#print axioms paper_cavity_comparison_finite_derivatives
end GaussianEllipsoid.PaperIsonormalCavity
