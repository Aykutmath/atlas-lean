import BMSaddleRawModel
import UCNormalizedRows
import UCEscapeStatistic

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments BMGeometry BMSaddle MeasureTheory
namespace UCEscape

/-- The source matrix in the column-indexed Frobenius Hilbert-space model. -/
def sourceFrobenius {d : ℕ} (A : GaussianEllipsoid.Square d) : HMat d :=
  (WithLp.equiv 2 _).symm (fun j => (WithLp.equiv 2 _).symm (fun i => A i j))

@[simp] theorem sourceFrobenius_apply {d : ℕ} (A : GaussianEllipsoid.Square d) (j i : Fin d) :
    sourceFrobenius A j i = A i j := rfl

theorem sourceFrobenius_norm {d : ℕ} (A : GaussianEllipsoid.Square d) :
    ‖sourceFrobenius A‖ = GaussianEllipsoid.frobeniusNorm A := by
  apply (sq_eq_sq₀ (norm_nonneg _) (frobeniusNorm_nonneg _)).mp
  rw [frobenius_norm_sq, frobeniusNorm_sq]
  change (∑ j,∑ i,(A i j)^2) = ∑ i,∑ j,(A i j)^2
  exact Finset.sum_comm

theorem sourceFrobenius_psd {d : ℕ} (A : GaussianEllipsoid.Square d) :
    IsPSD (frobeniusOperator (sourceFrobenius A)) ↔ A.PosSemidef := by
  rw [← opMatrix_posSemidef_iff]
  simp only [opMatrix, operatorFrobenius_frobeniusOperator]
  rfl

theorem sourceFrobenius_mem_psdUnit {d : ℕ} (A : GaussianEllipsoid.Square d)
    (hA : A.PosSemidef) (hF : frobeniusNorm A = 1) : sourceFrobenius A ∈ psdUnit d := by
  refine ⟨(sourceFrobenius_psd A).mpr hA, ?_⟩
  simpa only [Metric.mem_sphere, dist_zero_right, sourceFrobenius_norm] using hF

/-- Exact equality of every Gaussian row, with no symmetry or dimension restriction. -/
theorem gaussianRow_eq_measurement {n d : ℕ} (A : GaussianEllipsoid.Square d)
    (z : BMSaddle.Raw n d) (i : Fin n) :
    GaussianEllipsoid.UCNormalizedRows.gaussianRow A (z i) =
      BMSaddle.measurement (BMSaddle.rawSample n d z) (sourceFrobenius A) i := by
  unfold GaussianEllipsoid.UCNormalizedRows.gaussianRow
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, measurement_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change A k j*z i (finProdFinEquiv (k,j)) = z i (finProdFinEquiv (k,j))*A k j
  ring

/-- The complete joint Gaussian sample law is transported, not just marginals. -/
theorem gaussianRows_preserving (n d : ℕ) :
    MeasurePreserving (BMSaddle.rawSample n d)
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d))))
      (BMSaddle.sampleLaw n d) := BMSaddle.rawSample_preserving n d

/-- Transport of any measurable event in the matrix Gaussian experiment. -/
theorem gaussianRows_event (n d : ℕ) (E : Set (BMSaddle.Sample n d))
    (hE : MeasurableSet E) :
    (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))).real
      {z | BMSaddle.rawSample n d z ∈ E} = (BMSaddle.sampleLaw n d).real E :=
  (gaussianRows_preserving n d).measureReal_preimage hE.nullMeasurableSet

/-- Transport of every integrable observable of the complete sample. -/
theorem gaussianRows_integral (n d : ℕ) (f : BMSaddle.Sample n d → ℝ)
    (hf : AEStronglyMeasurable f (BMSaddle.sampleLaw n d)) :
    (∫ z, f (BMSaddle.rawSample n d z)
      ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))) =
      ∫ X, f X ∂BMSaddle.sampleLaw n d := by
  rw [← (gaussianRows_preserving n d).map_eq] at hf ⊢
  exact (integral_map (gaussianRows_preserving n d).measurable.aemeasurable hf).symm

#print axioms sourceFrobenius_mem_psdUnit
#print axioms gaussianRow_eq_measurement
#print axioms gaussianRows_preserving
#print axioms gaussianRows_event
#print axioms gaussianRows_integral
end UCEscape
