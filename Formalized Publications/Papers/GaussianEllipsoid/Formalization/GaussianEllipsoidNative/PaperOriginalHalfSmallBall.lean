import PaperHalfSmallBall

noncomputable section
open MeasureTheory GaussianMixedNormHelpers GaussianTensorMoments GaussianBilinearTransport
open GaussianEllipsoid GaussianEllipsoid.SmallBall GaussianEllipsoid.ProjectedClusters GaussianPairedBlocks
open scoped BigOperators
namespace GaussianTensorMoments

/-- The actual paper observation sample and literal first/last halves, with
all dimensions and centers. The exact product-law adapter is part of the proof. -/
theorem paper_original_half_determinant_small_ball (d n : ℕ) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (z : Fin n → ℝ) (hz2 : euclidNorm z=1) (hz : ‖z‖ ≤ θ/Real.sqrt (d:ℝ))
    (M : FrobeniusMatrix (d/2) (d/2)) (t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
      {x | ‖paperBilinearOperator d n x ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) z)-M‖ ≤
        t*Real.sqrt (d:ℝ)} ≤ (12*t)^((d/2)*(d/2)) := by
  by_cases hh0 : d/2=0
  · rw [show (12*t)^((d/2)*(d/2)) = 1 by simp [hh0]]
    exact measureReal_le_one
  have hh : 0 < d/2 := Nat.pos_of_ne_zero hh0
  let E : Set (BilinearSample (d/2) n) :=
    {p | ‖bilinearScaled (d:ℝ) (d/2) n z p-M‖ ≤ t*Real.sqrt (d:ℝ)}
  have hE : MeasurableSet E := measurableSet_le
    ((measurable_bilinearScaled (d:ℝ) (d/2) n z).sub_const M).norm measurable_const
  have hp := (flatToSmallBall_preserving n (d/2)).comp
    (splitCoordinateRows_preserving n (paperBlockLeft d) (paperBlockRight d) (paperBlock_disjoint d))
  have he : {x | ‖paperBilinearOperator d n x ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) z)-M‖ ≤
        t*Real.sqrt (d:ℝ)} =
      (fun x => flatToSmallBall n (d/2)
        (splitCoordinateRows n (paperBlockLeft d) (paperBlockRight d) x)) ⁻¹' E := by
    ext x
    change _ ↔ ‖bilinearScaled (d:ℝ) (d/2) n z
      (flatToSmallBall n (d/2) (splitCoordinateRows n (paperBlockLeft d) (paperBlockRight d) x))-M‖ ≤ _
    have hobs := bilinearScaled_flatToSmallBall n (d/2) d hh
      (splitCoordinateRows n (paperBlockLeft d) (paperBlockRight d) x)
      ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) z)
    simp only [MeasurableEquiv.toLp_apply,WithLp.ofLp_toLp] at hobs
    rw [hobs]
    rfl
  rw [he]
  exact (hp.measureReal_preimage hE.nullMeasurableSet).le.trans
    (paper_half_determinant_small_ball d n θ hθ0 hθ z hz2 hz M t ht)

end GaussianTensorMoments
#print axioms GaussianTensorMoments.paper_original_half_determinant_small_ball
