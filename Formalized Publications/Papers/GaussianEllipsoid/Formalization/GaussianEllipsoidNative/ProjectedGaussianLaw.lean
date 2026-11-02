import GaussianSelectedColumns
import GaussianCoisometry
import GaussianBilinearContinuity
import GaussianBilinearSmallBall

noncomputable section
open MeasureTheory Module
open GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.ProjectedClusters

/-- Regroup an actual flat iid Gaussian array into Euclidean sample vectors. -/
def entriesToRows (n h : ℕ) (x : GaussianEntries n h) : Fin n → Euclid h :=
  fun i => (MeasurableEquiv.toLp 2 ((Fin h) → ℝ)) (fun a => x (i,a))

def rowsToEntries (n h : ℕ) (x : Fin n → Euclid h) : GaussianEntries n h :=
  fun p => x p.1 p.2

theorem measurable_entriesToRows (n h : ℕ) : Measurable (entriesToRows n h) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).measurable.comp
    (measurable_pi_iff.mpr (fun a => measurable_pi_apply (i,a)))

theorem measurable_rowsToEntries (n h : ℕ) : Measurable (rowsToEntries n h) :=
  measurable_pi_iff.mpr (fun p =>
    (measurable_pi_apply p.2).comp
      (((MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).symm).measurable.comp
        (measurable_pi_apply p.1)))

theorem entriesToRows_preserving (n h : ℕ) :
    MeasurePreserving (entriesToRows n h) (gaussianProductLaw (Fin n × Fin h))
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin h))) := by
  have hc : MeasurePreserving (fun x : GaussianEntries n h => fun i a => x (i,a))
      (gaussianProductLaw (Fin n × Fin h))
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin h))) :=
    ⟨measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr
      (fun a => measurable_pi_apply (i,a))), gaussianProductLaw_map_curry⟩
  have he := measurePreserving_pi
    (fun _ : Fin n => gaussianProductLaw (Fin h))
    (fun _ : Fin n => euclideanGaussianLaw (Fin h))
    (f := fun _ => (MeasurableEquiv.toLp 2 ((Fin h) → ℝ)))
    (fun _ => ⟨(MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).measurable, rfl⟩)
  exact he.comp hc

theorem rowsToEntries_preserving (n h : ℕ) :
    MeasurePreserving (rowsToEntries n h)
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin h)))
      (gaussianProductLaw (Fin n × Fin h)) := by
  refine ⟨measurable_rowsToEntries n h, ?_⟩
  rw [← (entriesToRows_preserving n h).map_eq,
    Measure.map_map (measurable_rowsToEntries n h) (measurable_entriesToRows n h)]
  have hh : rowsToEntries n h ∘ entriesToRows n h = id := rfl
  rw [hh, Measure.map_id]

/-- Apply a fixed rectangular linear map to each actual sample column. -/
def transformEntries {h k : ℕ} (n : ℕ) (U : Euclid h →L[ℝ] Euclid k)
    (x : GaussianEntries n h) : GaussianEntries n k :=
  rowsToEntries n k (fun i => U (entriesToRows n h x i))

theorem measurable_transformEntries {h k : ℕ} (n : ℕ) (U : Euclid h →L[ℝ] Euclid k) :
    Measurable (transformEntries n U) := by
  apply (measurable_rowsToEntries n k).comp
  apply measurable_pi_iff.mpr
  intro i
  exact U.continuous.measurable.comp
    ((measurable_pi_apply i).comp (measurable_entriesToRows n h))

/-- Actual Gaussian invariance for all columns simultaneously. -/
theorem transformEntries_preserving {h k : ℕ} (n : ℕ) (U : Euclid h →L[ℝ] Euclid k)
    (hU : U ∘L ContinuousLinearMap.adjoint U = ContinuousLinearMap.id ℝ _) :
    MeasurePreserving (transformEntries n U) (gaussianProductLaw (Fin n × Fin h))
      (gaussianProductLaw (Fin n × Fin k)) := by
  have hrow : MeasurePreserving U (euclideanGaussianLaw (Fin h))
      (euclideanGaussianLaw (Fin k)) :=
    ⟨U.continuous.measurable, SmallBall.euclideanGaussianLaw_map_coisometry U hU⟩
  have hpi := measurePreserving_pi
    (fun _ : Fin n => euclideanGaussianLaw (Fin h))
    (fun _ : Fin n => euclideanGaussianLaw (Fin k)) (f := fun _ => U) (fun _ => hrow)
  exact (rowsToEntries_preserving n k).comp (hpi.comp (entriesToRows_preserving n h))

/-- Independently transform the left and right Gaussian factors. -/
def transformSample {h k : ℕ} (n : ℕ) (U V : Euclid h →L[ℝ] Euclid k)
    (x : GaussianEntries n h × GaussianEntries n h) :
    GaussianEntries n k × GaussianEntries n k :=
  (transformEntries n U x.1, transformEntries n V x.2)

theorem measurable_transformSample {h k : ℕ} (n : ℕ)
    (U V : Euclid h →L[ℝ] Euclid k) : Measurable (transformSample n U V) :=
  ((measurable_transformEntries n U).comp measurable_fst).prodMk
    ((measurable_transformEntries n V).comp measurable_snd)

/-- Exact joint Gaussian law after any fixed pair of coisometries. No
projection-law or independence hypothesis is assumed. -/
theorem transformSample_preserving {h k : ℕ} (n : ℕ)
    (U V : Euclid h →L[ℝ] Euclid k)
    (hU : U ∘L ContinuousLinearMap.adjoint U = ContinuousLinearMap.id ℝ _)
    (hV : V ∘L ContinuousLinearMap.adjoint V = ContinuousLinearMap.id ℝ _) :
    MeasurePreserving (transformSample n U V) (tensorGaussianLaw n h)
      (tensorGaussianLaw n k) :=
  (transformEntries_preserving n U hU).prod (transformEntries_preserving n V hV)

end GaussianEllipsoid.ProjectedClusters
