import GaussianSelectedColumns
import GaussianBilinearContinuity
import DisjointBilinearSmallBall

noncomputable section
open MeasureTheory
open GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoid GaussianEllipsoid.SmallBall
namespace GaussianBilinearTransport

/-- The exact regrouping from the continuity sample law to the small-ball law. -/
def flatToSmallBall (n r : ℕ)
    (z : GaussianEntries n r × GaussianEntries n r) : BilinearSample r n :=
  (fun i j => z.1 (i,j), (MeasurableEquiv.toLp 2 ((Fin n × Fin r) → ℝ)) z.2)

def smallBallToFlat (n r : ℕ) (z : BilinearSample r n) :
    GaussianEntries n r × GaussianEntries n r :=
  (fun p => z.1 p.1 p.2, ((MeasurableEquiv.toLp 2 ((Fin n × Fin r) → ℝ)).symm) z.2)

theorem flatToSmallBall_measurable (n r : ℕ) : Measurable (flatToSmallBall n r) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr
      (fun j => (measurable_pi_apply (i,j)).comp measurable_fst))
  · exact (MeasurableEquiv.toLp 2 ((Fin n × Fin r) → ℝ)).measurable.comp measurable_snd

theorem smallBallToFlat_measurable (n r : ℕ) : Measurable (smallBallToFlat n r) := by
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro p
    have h : Measurable (fun x : BilinearSample r n => x.1 p.1) :=
      (measurable_pi_apply p.1).comp measurable_fst
    exact (measurable_pi_apply p.2).comp h
  · exact ((MeasurableEquiv.toLp 2 ((Fin n × Fin r) → ℝ)).symm).measurable.comp measurable_snd

theorem flatToSmallBall_preserving (n r : ℕ) :
    MeasurePreserving (flatToSmallBall n r) (tensorGaussianLaw n r)
      (bilinearGaussianSampleLaw r n) := by
  have hl : MeasurePreserving
      (fun z : (Fin n × Fin r) → ℝ => fun i j => z (i,j))
      (gaussianProductLaw (Fin n × Fin r))
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin r))) :=
    ⟨measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j => measurable_pi_apply (i,j))),
      gaussianProductLaw_map_curry⟩
  have hr : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin r) → ℝ))
      (gaussianProductLaw (Fin n × Fin r)) (euclideanGaussianLaw (Fin n × Fin r)) :=
    ⟨(MeasurableEquiv.toLp 2 ((Fin n × Fin r) → ℝ)).measurable, rfl⟩
  exact hl.prod hr

theorem smallBallToFlat_flatToSmallBall (n r : ℕ)
    (z : GaussianEntries n r × GaussianEntries n r) :
    smallBallToFlat n r (flatToSmallBall n r z) = z := by
  ext p <;> rfl

theorem flatToSmallBall_smallBallToFlat (n r : ℕ) (z : BilinearSample r n) :
    flatToSmallBall n r (smallBallToFlat n r z) = z := by
  ext i j <;> rfl

theorem smallBallToFlat_preserving (n r : ℕ) :
    MeasurePreserving (smallBallToFlat n r) (bilinearGaussianSampleLaw r n)
      (tensorGaussianLaw n r) := by
  refine ⟨smallBallToFlat_measurable n r, ?_⟩
  rw [← (flatToSmallBall_preserving n r).map_eq,
    Measure.map_map (smallBallToFlat_measurable n r) (flatToSmallBall_measurable n r)]
  have h : (smallBallToFlat n r) ∘ (flatToSmallBall n r) = id := by
    funext z
    exact smallBallToFlat_flatToSmallBall n r z
  rw [h, Measure.map_id]

/-- Both representations have literally the same d-scaled matrix observable. -/
theorem bilinearScaled_flatToSmallBall (n r d : ℕ) (hr : 0 < r)
    (z : GaussianEntries n r × GaussianEntries n r) (y : EuclideanSpace ℝ (Fin n)) :
    bilinearScaled (d:ℝ) r n (fun i => y i) (flatToSmallBall n r z) =
      gaussianBilinearOperator n r d z y := by
  ext j i
  change frobeniusToMatrix (bilinearScaled (d:ℝ) r n (fun i => y i)
    (flatToSmallBall n r z)) i j =
      frobeniusToMatrix (gaussianBilinearOperator n r d z y) i j
  rw [bilinearScaled_entry r n hr, gaussianBilinearOperator_apply]
  dsimp [flatToSmallBall]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  change y k * z.1 (k,i) * z.2 (k,j) = y k * (z.1 (k,i) * z.2 (k,j))
  ring

#print axioms flatToSmallBall_preserving
#print axioms smallBallToFlat_preserving
#print axioms bilinearScaled_flatToSmallBall
end GaussianBilinearTransport
