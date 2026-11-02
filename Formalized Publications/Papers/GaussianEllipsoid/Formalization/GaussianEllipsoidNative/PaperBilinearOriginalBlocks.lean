import PaperBilinearAspect
import GaussianCoordinateSplit
import GaussianBilinearMeasurability

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianTensorTrace Filter
open GaussianMixedNormHelpers GaussianEllipsoid.ProjectedClusters
open scoped Topology BigOperators
namespace GaussianTensorMoments

/-- The first floor(d/2) coordinates in the paper. -/
def paperBlockLeft (d : ℕ) : Fin (d/2) ↪ Fin d where
  toFun j := ⟨j.val, by omega⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun z : Fin d => z.val) h)

/-- The last floor(d/2) coordinates; the middle coordinate is discarded for odd d. -/
def paperBlockRight (d : ℕ) : Fin (d/2) ↪ Fin d where
  toFun j := ⟨d-d/2+j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun z : Fin d => z.val) h
    change d-d/2+i.val = d-d/2+j.val at hh
    omega

theorem paperBlock_disjoint (d : ℕ) (i j : Fin (d/2)) :
    paperBlockLeft d i ≠ paperBlockRight d j := by
  intro h
  have hh := congrArg (fun z : Fin d => z.val) h
  change i.val = d-d/2+j.val at hh
  omega

/-- Literal original Gaussian observations, with exactly the paper's first/last
halves and normalization. -/
def paperBilinearOperator (d n : ℕ) (x : Fin n → Euclid d) :=
  gaussianBilinearOperator n (d/2) d
    (splitCoordinateRows n (paperBlockLeft d) (paperBlockRight d) x)

theorem paperBilinearOperator_entries (d n : ℕ) (x : Fin n → Euclid d)
    (y : Euclid n) (a b : Fin (d/2)) :
    frobeniusToMatrix (paperBilinearOperator d n x y) a b =
      (Real.sqrt d)⁻¹ * ∑ i, y i * (x i (paperBlockLeft d a)*x i (paperBlockRight d b)) := by
  exact gaussianBilinearOperator_apply n (d/2) d
    (splitCoordinateRows n (paperBlockLeft d) (paperBlockRight d) x) y a b

theorem paperBilinearOperator_bad_probability_eq (d n : ℕ) (L : ℝ) :
    (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
      {x | L*Real.sqrt d < ‖paperBilinearOperator d n x‖} =
      (tensorGaussianLaw n (d/2)).real
      {z | L*Real.sqrt d < ‖gaussianBilinearOperator n (d/2) d z‖} := by
  exact (splitCoordinateRows_preserving n (paperBlockLeft d) (paperBlockRight d)
    (paperBlock_disjoint d)).measureReal_preimage
      (gaussianBilinearOperator_bad_measurableSet n (d/2) d L).nullMeasurableSet

/-- Exact original-block fixed-aspect statement of paper main-lemma-4-2.
The stronger fixed-constant high-probability conclusion implies O_P(sqrt d). -/
theorem paper_bilinear_operator_arbitrary_aspect (A : ℝ) (hA : 0 < A) :
    ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ → ℕ,
      (∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) →
      Tendsto (fun d =>
        (Measure.pi (fun _ : Fin (n d) => euclideanGaussianLaw (Fin d))).real
          {x | L*Real.sqrt d < ‖paperBilinearOperator d (n d) x‖})
        atTop (𝓝 0) := by
  obtain ⟨L,hL,hlim⟩ := gaussianBilinearOperator_arbitrary_aspect_tendsto_zero A hA
  refine ⟨L,hL,?_⟩
  intro n hn
  simpa only [paperBilinearOperator_bad_probability_eq] using hlim n hn

end GaussianTensorMoments
#print axioms GaussianTensorMoments.paper_bilinear_operator_arbitrary_aspect
