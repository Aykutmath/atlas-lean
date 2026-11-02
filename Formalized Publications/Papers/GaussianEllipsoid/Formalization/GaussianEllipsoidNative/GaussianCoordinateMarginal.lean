import GaussianRadialMoments

noncomputable section
open MeasureTheory ProbabilityTheory
open GaussianTensorMoments
namespace GaussianMixedNormHelpers

/-- An injective coordinate subfamily of the actual iid law has the smaller iid law. -/
theorem gaussianProductLaw_map_subfamily {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) :
    (gaussianProductLaw ι).map (fun x : ι → ℝ => fun k : κ => x (f k)) =
      gaussianProductLaw κ := by
  have hi := gaussianProductLaw_iIndepFun (ι := ι) |>.precomp hf
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun k : κ => (measurable_pi_apply (f k)).aemeasurable)).mp hi
  have hmarg : (fun k : κ => (gaussianProductLaw ι).map (fun x : ι → ℝ => x (f k))) =
      (fun _ : κ => gaussianReal 0 1) := by
    funext k
    exact gaussianProductLaw_coordinate (f k)
  rw [hmarg] at h
  exact h

/-- Coordinate restriction in the Euclidean-space realizations. -/
def euclideanCoordinateSubfamily {ι κ : Type*} (f : κ → ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ :=
  (MeasurableEquiv.toLp 2 (κ → ℝ)) (fun k => x (f k))

@[simp] theorem euclideanCoordinateSubfamily_apply {ι κ : Type*} (f : κ → ι)
    (x : EuclideanSpace ℝ ι) (k : κ) :
    euclideanCoordinateSubfamily f x k = x (f k) := rfl

/-- Every fixed injective coordinate projection preserves the appropriate
standard Gaussian laws, proved by the actual product-measure marginal. -/
theorem euclideanGaussianLaw_map_subfamily {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) :
    (euclideanGaussianLaw ι).map (euclideanCoordinateSubfamily f) =
      euclideanGaussianLaw κ := by
  have hp : Measurable (fun x : ι → ℝ => fun k : κ => x (f k)) :=
    measurable_pi_lambda _ (fun k => measurable_pi_apply (f k))
  have hE : Measurable (euclideanCoordinateSubfamily f) := by
    change Measurable ((MeasurableEquiv.toLp 2 (κ → ℝ)) ∘
      (fun x : ι → ℝ => fun k : κ => x (f k)) ∘ (MeasurableEquiv.toLp 2 (ι → ℝ)).symm)
    exact (MeasurableEquiv.toLp 2 (κ → ℝ)).measurable.comp
      (hp.comp (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable)
  unfold euclideanGaussianLaw
  rw [Measure.map_map hE (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable]
  have heq : euclideanCoordinateSubfamily f ∘ (MeasurableEquiv.toLp 2 (ι → ℝ)) =
      (MeasurableEquiv.toLp 2 (κ → ℝ)) ∘ (fun x : ι → ℝ => fun k : κ => x (f k)) := by
    rfl
  rw [heq, ← Measure.map_map (MeasurableEquiv.toLp 2 (κ → ℝ)).measurable hp,
    gaussianProductLaw_map_subfamily f hf]

/-- Squared norm of any nonempty injective coordinate block has its exact gamma law. -/
theorem euclideanGaussianLaw_map_subfamily_norm_sq {ι κ : Type*}
    [Fintype ι] [Fintype κ] [Nonempty κ] (f : κ → ι) (hf : Function.Injective f) :
    (euclideanGaussianLaw ι).map
      (fun x : EuclideanSpace ℝ ι => ‖euclideanCoordinateSubfamily f x‖ ^ 2) =
        gammaMeasure ((Fintype.card κ : ℝ) / 2) (1 / 2) := by
  have hE : Measurable (euclideanCoordinateSubfamily f) := by
    change Measurable ((MeasurableEquiv.toLp 2 (κ → ℝ)) ∘
      (fun x : ι → ℝ => fun k : κ => x (f k)) ∘ (MeasurableEquiv.toLp 2 (ι → ℝ)).symm)
    exact (MeasurableEquiv.toLp 2 (κ → ℝ)).measurable.comp
      ((measurable_pi_lambda _ (fun k => measurable_pi_apply (f k))).comp
        (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable)
  rw [show (fun x : EuclideanSpace ℝ ι => ‖euclideanCoordinateSubfamily f x‖ ^ 2) =
      (fun y : EuclideanSpace ℝ κ => ‖y‖ ^ 2) ∘ euclideanCoordinateSubfamily f from rfl,
    ← Measure.map_map (by fun_prop) hE,
    euclideanGaussianLaw_map_subfamily f hf, euclideanGaussianLaw_map_norm_sq]

end GaussianMixedNormHelpers
