import ProjectedBilinearObservable
import ProjectedClusterArithmetic
import SubspaceCoordinateEmbedding

noncomputable section
open MeasureTheory Module
open GaussianMixedNormHelpers GaussianTensorMoments GaussianPairedBlocks GaussianBilinearTransport
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoid.ProjectedClusters

def projectedBilinear {h : ℕ} (P Q : Euclid h →L[ℝ] Euclid h) (n d : ℕ)
    (z : GaussianEntries n h × GaussianEntries n h) (u : Euclid n) : FrobeniusMatrix h h :=
  operatorFrobenius (P ∘L frobeniusOperator (gaussianBilinearOperator n h d z u) ∘L Q)

theorem measurable_gaussianBilinear (n h d : ℕ) (hh : 0 < h) (u : Euclid n) :
    Measurable (fun z => gaussianBilinearOperator n h d z u) := by
  have hh' := measurable_flatBilinear (d : ℝ) h n (fun i => u i)
  have he : flatBilinear (d : ℝ) h n (fun i => u i) =
      (fun z => gaussianBilinearOperator n h d z u) := by
    funext z
    exact bilinearScaled_flatToSmallBall n h d hh z u
  rwa [he] at hh'

theorem measurable_projectedBilinear {h : ℕ} (n d : ℕ) (hh : 0 < h)
    (u : Euclid n) {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Ω → Euclid h →L[ℝ] Euclid h) (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (fun p : Ω × (GaussianEntries n h × GaussianEntries n h) =>
      projectedBilinear (P p.1) (Q p.1) n d p.2 u) := by
  apply (continuous_operatorFrobenius h h).measurable.comp
  have hB : Measurable (fun p : Ω × (GaussianEntries n h × GaussianEntries n h) =>
      frobeniusOperator (gaussianBilinearOperator n h d p.2 u)) :=
    ((continuous_frobeniusOperator h h).measurable.comp
    (measurable_gaussianBilinear n h d hh u)).comp measurable_snd
  have hc : Continuous (fun p : (Euclid h →L[ℝ] Euclid h) × (Euclid h →L[ℝ] Euclid h) =>
      p.1 ∘L p.2) := by fun_prop
  exact hc.measurable.comp ((hP.comp measurable_fst).prodMk
    (hc.measurable.comp (hB.prodMk (hQ.comp measurable_fst))))

/-- Every fixed pair of residual subspaces has the real Gaussian block lower
tail, with no law or conditional-independence assumption. -/
theorem projected_nuclear_paired_smallball {n h k r s d : ℕ}
    (W Z : Submodule ℝ (Euclid h)) (hkW : k ≤ finrank ℝ W) (hkZ : k ≤ finrank ℝ Z)
    (hk : 0 < k) (hr : 0 < r) (hrs : r = 2*s)
    (u : Euclid n) {σ : ℝ} (hσ : 0 < σ) (hd : 0 < d)
    (husum : ∑ i, (u i)^2 = σ^2)
    (hucap : ∀ i, (u i)^2 ≤ σ^2 * (2*(r:ℝ))⁻¹) :
    tensorGaussianLaw n h
      {z | spectralNuclearNorm (projectedBilinear (W.subtypeL ∘L W.orthogonalProjection)
        (Z.subtypeL ∘L Z.orthogonalProjection) n d z u) ≤
          ((k/r : ℕ) : ℝ)/2 * blockThreshold σ d r} ≤
      ENNReal.ofReal (Real.exp (-((k/r : ℕ):ℝ)*(r:ℝ)^2/4)) := by
  let U := subspaceEmbedding W hkW
  let V := subspaceEmbedding Z hkZ
  let f := transformSample n (ContinuousLinearMap.adjoint U) (ContinuousLinearMap.adjoint V)
  have hp : MeasurePreserving f (tensorGaussianLaw n h) (tensorGaussianLaw n k) := by
    apply transformSample_preserving
    · simpa only [ContinuousLinearMap.adjoint_adjoint] using subspaceEmbedding_adjoint_comp W hkW
    · simpa only [ContinuousLinearMap.adjoint_adjoint] using subspaceEmbedding_adjoint_comp Z hkZ
  let E : Set (GaussianEntries n k × GaussianEntries n k) :=
    {z | spectralNuclearNorm (gaussianBilinearOperator n k d z u) ≤
      ((k/r : ℕ):ℝ)/2 * blockThreshold σ d r}
  have hE : MeasurableSet E := measurableSet_le
    ((continuous_spectralNuclear k k).measurable.comp (measurable_gaussianBilinear n k d hk u))
    measurable_const
  have hevent : tensorGaussianLaw n k E ≤
      ENNReal.ofReal (Real.exp (-((k/r : ℕ):ℝ)*(r:ℝ)^2/4)) := by
    have hb := gaussianBilinearOperator_paired_smallball (n := n) (d := d)
      (consecutiveBlocks k r) (consecutiveBlocks k r) hk hr hrs
      0 (fun i => u i) (fun _ => by simp) hσ hd husum hucap
    simp only [zero_add] at hb
    exact measure_le_of_real_le _ _ hb
  have hsub : {z | spectralNuclearNorm (projectedBilinear (W.subtypeL ∘L W.orthogonalProjection)
        (Z.subtypeL ∘L Z.orthogonalProjection) n d z u) ≤
          ((k/r : ℕ) : ℝ)/2 * blockThreshold σ d r} ⊆ f ⁻¹' E := by
    intro z hz
    have hc := spectralNuclear_compression_le (ContinuousLinearMap.adjoint U)
      ((W.subtypeL ∘L W.orthogonalProjection) ∘L
        frobeniusOperator (gaussianBilinearOperator n h d z u) ∘L
        (Z.subtypeL ∘L Z.orthogonalProjection)) V
      (by simpa [U] using subspaceEmbedding_norm_le_one W hkW)
      (subspaceEmbedding_norm_le_one Z hkZ)
    have heq : ContinuousLinearMap.adjoint U ∘L
        ((W.subtypeL ∘L W.orthogonalProjection) ∘L
        frobeniusOperator (gaussianBilinearOperator n h d z u) ∘L
        (Z.subtypeL ∘L Z.orthogonalProjection)) ∘L V =
        frobeniusOperator (gaussianBilinearOperator n k d (f z) u) := by
      rw [gaussianBilinearOperator_transformSample]
      simp only [ContinuousLinearMap.adjoint_adjoint]
      calc
        _ = (ContinuousLinearMap.adjoint U ∘L (W.subtypeL ∘L W.orthogonalProjection)) ∘L
            frobeniusOperator (gaussianBilinearOperator n h d z u) ∘L
            ((Z.subtypeL ∘L Z.orthogonalProjection) ∘L V) := by
              simp only [ContinuousLinearMap.comp_assoc]
        _ = _ := by rw [subspaceEmbedding_adjoint_comp_projector, subspaceProjector_comp_embedding]
    rw [heq, operatorFrobenius_frobeniusOperator] at hc
    exact hc.trans hz
  calc
    _ ≤ tensorGaussianLaw n h (f ⁻¹' E) := measure_mono hsub
    _ = tensorGaussianLaw n k E := by rw [← hp.map_eq, Measure.map_apply hp.measurable hE]
    _ ≤ _ := hevent

/-- Actual fixed-projection regular-cluster Gaussian nuclear lower tail. The
constants are explicit, and no Gaussian-law or independence premise remains. -/
theorem projected_regular_cluster {n h d : ℕ}
    (W Z : Submodule ℝ (Euclid h))
    (hW : (d : ℝ) / 4 ≤ finrank ℝ W) (hZ : (d : ℝ) / 4 ≤ finrank ℝ Z)
    (u : Euclid n) {σ m R : ℝ} (hσ : 0 < σ)
    (husum : ∑ i, (u i)^2 = σ^2) (hm : m = ∑ i, |u i|)
    (hRdef : R = m^2 / σ^2) (hR : 4096 ≤ R) (hRd : R ≤ d)
    (hcap : ∀ i, |u i| ≤ 16 * σ / Real.sqrt R) :
    tensorGaussianLaw n h
      {z | spectralNuclearNorm (projectedBilinear (W.subtypeL ∘L W.orthogonalProjection)
        (Z.subtypeL ∘L Z.orthogonalProjection) n d z u) <
          projectedConstant * Real.sqrt d * m} ≤
      ENNReal.ofReal (Real.exp (-(d : ℝ)*R/65536)) := by
  let k := min (finrank ℝ W) (finrank ℝ Z)
  have hk : (d : ℝ) / 4 ≤ k := by
    dsimp [k]
    rw [Nat.cast_min]
    exact le_min hW hZ
  have hd : 0 < d := by exact_mod_cast (by linarith : (0 : ℝ) < d)
  have hk0 : 0 < k := by exact_mod_cast (by have hdp : (0:ℝ) < d := Nat.cast_pos.mpr hd; linarith : (0:ℝ) < k)
  have hms : m = σ * Real.sqrt R := by
    have hm0 : 0 ≤ m := by rw [hm]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    apply (sq_eq_sq₀ hm0 (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ R), hRdef]
    field_simp
  have hb := projected_nuclear_paired_smallball W Z (Nat.min_le_left _ _) (Nat.min_le_right _ _)
    hk0 (by have := (regularBlockSize_bounds hR).1; omega : 0 < regularBlockSize R)
    (show regularBlockSize R = 2 * regularBlockHalf R from rfl)
    u hσ hd husum (fun i => regularBlock_coefficient_cap hR hσ (hcap i))
  apply (measure_mono ?_).trans (hb.trans ?_)
  · intro z hz
    exact le_trans hz.le (regularBlock_threshold hR hRd hk hσ hms)
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have he := regularBlock_exponent hR hRd hk
    linarith

end GaussianEllipsoid.ProjectedClusters
