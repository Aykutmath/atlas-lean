import UCHeadCompression
import UCHeadNuisance
import UCDiffuseFiniteModel
import GaussianEllipsoid.ConicNets

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid BMGeometry
open GaussianEllipsoid.UCDiffuseFiniteModel
namespace UCEscape

lemma split_head_coordinate {d j n : ℕ} (U : Euclid j →ₗᵢ[ℝ] Euclid d)
    (x : GaussianEllipsoid.Sample d n) (i : Fin n) (k : Fin j) :
    (gaussianSampleBlockSplit (frameCompletion U) n x).1 i k =
      U.toContinuousLinearMap.adjoint ((WithLp.equiv 2 _).symm (x i)) k := by
  have h := congrArg (fun z : Euclid j × Euclid (d-j) => z.1 k)
    (frameCompletion_blocks U ((WithLp.equiv 2 _).symm (x i)))
  exact h

lemma split_tail_coordinate {d j n : ℕ} (U : Euclid j →ₗᵢ[ℝ] Euclid d)
    (x : GaussianEllipsoid.Sample d n) (i : Fin n) (k : Fin (d-j)) :
    (gaussianSampleBlockSplit (frameCompletion U) n x).2 i k =
      (frameComplement U).toContinuousLinearMap.adjoint ((WithLp.equiv 2 _).symm (x i)) k := by
  have h := congrArg (fun z : Euclid j × Euclid (d-j) => z.2 k)
    (frameCompletion_blocks U ((WithLp.equiv 2 _).symm (x i)))
  exact h

lemma source_compressed_row {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d)
    (A : GaussianEllipsoid.Square d) (hA : A.PosSemidef)
    (hsupp : ∀ x, sourceOperator A x ∈ LinearMap.range V.toLinearMap)
    (x : GaussianEllipsoid.Vector d) :
    (quadratic A x-Matrix.trace A)/Real.sqrt 2 =
      (quadratic (opMatrix (compress V (sourceOperator A)))
        (fun i => V.toContinuousLinearMap.adjoint ((WithLp.equiv 2 _).symm x) i)-
        Matrix.trace (opMatrix (compress V (sourceOperator A))))/Real.sqrt 2 := by
  have h := compressed_measurement_row V (sourceOperator A)
    ((sourceFrobenius_psd A).mpr hA) hsupp ((WithLp.equiv 2 _).symm x)
  simpa only [opMatrix_sourceFrobenius, WithLp.equiv_symm_apply, WithLp.ofLp_toLp] using h

/-- An actual supported head/diffuse-tail failure belongs to the fixed-frame
measurable conditioning event. Nuisance coefficients are explicit; no choice
or measurability hypothesis is introduced. -/
theorem fixed_frame_witness_mem_bad {d j n : ℕ}
    (U : Euclid j →ₗᵢ[ℝ] Euclid d) (x : GaussianEllipsoid.Sample d n)
    (H D : GaussianEllipsoid.Square d) (hH : H.PosSemidef) (hD : D.PosSemidef)
    (hHead : ∀ y, sourceOperator H y ∈ LinearMap.range U.toLinearMap)
    (hTail : ∀ y, sourceOperator D y ∈ (LinearMap.range U.toLinearMap)ᗮ)
    (hF : frobeniusNorm D = 1) {τ ρ c : ℝ} (hOp : matrixOpNorm D ≤ τ)
    (hρ : 0 < ρ) (hbad : conicMargin x (H+ρ • D) < ρ*c) :
    gaussianSampleBlockSplit (frameCompletion U) n x ∈
      headTailQuadraticBadEvent (sourceDiffuseClass (d-j) τ) c := by
  let V := frameComplement U
  let HH := opMatrix (compress U (sourceOperator H))
  let DD := opMatrix (compress V (sourceOperator D))
  let z := gaussianSampleBlockSplit (frameCompletion U) n x
  have hTs : ∀ y, sourceOperator D y ∈ LinearMap.range V.toLinearMap := by
    intro y
    rw [show V = frameComplement U from rfl, frameComplement_range]
    exact hTail y
  have hFD : ‖operatorFrobenius (sourceOperator D)‖ = 1 := by
    rw [operatorFrobenius_frobeniusOperator, sourceFrobenius_norm, hF]
  have hOD : ‖sourceOperator D‖ ≤ τ := by
    rw [← matrixOpNorm_opMatrix, opMatrix_sourceFrobenius]
    exact hOp
  have hDD : DD ∈ sourceDiffuseClass (d-j) τ :=
    compressed_diffuse_constraints V (sourceOperator D) ((sourceFrobenius_psd D).mpr hD) hTs hFD hOD
  have hh (i : Fin n) : measurementQ x H i = measurementQ z.1 HH i := by
    have h := source_compressed_row U H hH hHead (x i)
    change _ = (quadratic HH _-Matrix.trace HH)/Real.sqrt 2
    rw [show z.1 i = fun k => U.toContinuousLinearMap.adjoint ((WithLp.equiv 2 _).symm (x i)) k by
      funext k; exact split_head_coordinate U x i k]
    exact h
  have ht (i : Fin n) : measurementQ x D i = measurementQ z.2 DD i := by
    have h := source_compressed_row V D hD hTs (x i)
    change _ = (quadratic DD _-Matrix.trace DD)/Real.sqrt 2
    rw [show z.2 i = fun k => V.toContinuousLinearMap.adjoint ((WithLp.equiv 2 _).symm (x i)) k by
      funext k; exact split_tail_coordinate U x i k]
    exact h
  let b := mean (measurementQ x (H+ρ • D))/ρ
  refine ⟨⟨DD,hDD⟩, -ρ⁻¹ • HH,b,?_⟩
  have he (i : Fin n) : measurementQ z.2 DD i - measurementQ z.1 (-ρ⁻¹ • HH) i-b =
      ρ⁻¹ * center (measurementQ x (H+ρ • D)) i := by
    rw [measurementQ_smul]
    change measurementQ z.2 DD i - (-ρ⁻¹ * measurementQ z.1 HH i)-b = _
    rw [← hh, ← ht]
    unfold center b measurementQ
    rw [quadratic_add, quadratic_smul, Matrix.trace_add, Matrix.trace_smul]
    simp only [smul_eq_mul]
    field_simp
    <;> ring
  change (∑ i, |measurementQ z.2 DD i-measurementQ z.1 (-ρ⁻¹ • HH) i-b|)/(n:ℝ) < c
  simp_rw [he, abs_mul, abs_of_pos (inv_pos.mpr hρ)]
  rw [← Finset.mul_sum]
  have hv : (ρ⁻¹ * ∑ i, |center (measurementQ x (H+ρ • D)) i|)/(n:ℝ) =
      ρ⁻¹*conicMargin x (H+ρ • D) := by
    unfold conicMargin l1Size
    ring
  rw [hv]
  have h := mul_lt_mul_of_pos_left hbad (inv_pos.mpr hρ)
  simpa only [← mul_assoc, inv_mul_cancel₀ hρ.ne', one_mul] using h

#print axioms fixed_frame_witness_mem_bad
end UCEscape
