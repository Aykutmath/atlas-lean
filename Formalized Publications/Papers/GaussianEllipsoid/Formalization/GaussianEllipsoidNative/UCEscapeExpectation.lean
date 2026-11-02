import UCEscapeValues
import UCCompactEscapeComparison
import UCPSDMinimumMean

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle BMGordon
namespace UCEscape

variable {J : Type} [Fintype J] [Nonempty J] [MetricSpace J] [DiscreteTopology J]
  {n d r : ℕ}

theorem projected_escape_comparison (hd : 0 < d) (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) :
    (∫ ω, BMGordonCompact.compactMinMax (escapeAuxiliary (d := d) U) ω ∂law n d) ≤
      ∫ ω, BMGordonCompact.compactMinMax (escapePrimary (d := d) U) ω ∂law n d := by
  letI : CompactSpace ↥(psdUnit d) := isCompact_iff_compactSpace.mp (psdUnit_compact d)
  letI : Nonempty ↥(psdUnit d) := (psdUnit_nonempty hd).to_subtype
  letI : Nonempty (UnitSample r) := unitSample_nonempty hr
  apply compact_escape_comparison (EscapeIndex J d) (UnitSample r)
    (fun p => (p.2 : HMat d)) (fun p => U p.1.1 p.2)
  · exact continuous_subtype_val.comp continuous_snd
  · have hU : Continuous (fun j : J => (U j).toContinuousLinearMap) := continuous_of_discreteTopology
    exact (hU.comp (continuous_fst.comp continuous_fst)).clm_apply
      (continuous_subtype_val.comp continuous_snd)
  · intro p
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property.2
  · intro p
    rw [(U p.1.1).norm_map, unitSample_norm]

theorem projectedEscape_integrable (hd : 0 < d)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) :
    Integrable (projectedEscape (d := d) U) (sampleLaw n d) :=
  GaussianVariance.lipschitz_integrable (projectedEscape_lipschitz hd U)

theorem primary_escape_mean (hd : 0 < d) (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) :
    (∫ ω, BMGordonCompact.compactMinMax (escapePrimary (d := d) U) ω ∂law n d) =
      ∫ X, projectedEscape (d := d) U X ∂sampleLaw n d := by
  simp_rw [escapePrimary_value hd hr]
  have hi := ((matrixBlock_preserving n d).integrable_comp
    (projectedEscape_integrable hd U).aestronglyMeasurable).mpr (projectedEscape_integrable hd U)
  simp only [Function.comp_def] at hi
  rw [integral_add hi (scalarBlock_integrable n d), scalarBlock_mean, add_zero]
  exact integral_comp_preserving (matrixBlock_preserving n d)
    (projectedEscape_integrable hd U).aestronglyMeasurable

theorem auxiliary_escape_mean (hd : 0 < d) (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) :
    (∫ ω, BMGordonCompact.compactMinMax (escapeAuxiliary (d := d) U) ω ∂law n d) =
      (∫ g, projectedNormMinimum n r U g ∂euclideanGaussianLaw (Fin n)) +
        ∫ z, psdMinimumRaw d z ∂GaussianTensorMoments.gaussianProductLaw (Fin d × Fin d) := by
  simp_rw [escapeAuxiliary_value hd hr]
  have hj : Integrable (projectedNormMinimum n r U) (euclideanGaussianLaw (Fin n)) := by
    rw [euclideanGaussianLaw_eq_stdGaussian]
    exact projectedNormMinimum_integrable n r U
  have hs := GaussianVariance.lipschitz_integrable (psdMinimumEuclidean_lipschitz hd)
  have hi := ((driftBlock_preserving n d).integrable_comp hj.aestronglyMeasurable).mpr hj
  have hk := ((widthBlock_preserving n d).integrable_comp hs.aestronglyMeasurable).mpr hs
  simp only [Function.comp_def] at hi hk
  change Integrable (fun ω : Space n d => psdMinimum d (widthMatrix ω)) (law n d) at hk
  rw [integral_add hi hk]
  congr 1
  · exact integral_comp_preserving (driftBlock_preserving n d) hj.aestronglyMeasurable
  · change (∫ ω, psdMinimum d ((frobeniusEquivEuclidean d d).symm (widthBlock ω)) ∂law n d) = _
    rw [integral_comp_preserving (widthBlock_preserving n d) hs.aestronglyMeasurable]
    rw [euclideanGaussianLaw, integral_map
      (MeasurableEquiv.toLp 2 ((Fin d × Fin d) → ℝ)).measurable.aemeasurable
      (psdMinimumEuclidean_lipschitz hd).continuous.aestronglyMeasurable]
    rfl

/-- Sharp retained-family mean escape. All Gaussian comparison and projection
inputs are proved; the finite family may have arbitrary dependent frames. -/
theorem projectedEscape_mean_lower (hd : 0 < d) (hr : 0 < r)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1-ε)*Real.sqrt r*(1-(Fintype.card J : ℝ)*Real.exp (-ε^2*(r:ℝ)/8)) -
        Real.sqrt ((d:ℝ)*(d+1)/4) ≤
      ∫ X, projectedEscape (d := d) U X ∂sampleLaw n d := by
  have h := projected_escape_comparison hd hr U
  rw [primary_escape_mean hd hr, auxiliary_escape_mean hd hr] at h
  have h1 := euclideanGaussian_projectedNormMinimum_expectation_lower n r U ε hε hε1
  have h2 := mean_psdMinimum_lower hd
  linarith

#print axioms projectedEscape_mean_lower
end UCEscape
