import ProjectedHeadProduct

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Module
open GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoid.ProjectedClusters

/-- Exact Section 7 bound on one original Gaussian sample space. The head and
current indices are only required to be disjoint; their independent product
law is a proved pushforward identity, never a premise. -/
theorem projected_regular_cluster_disjoint_samples {N p n h d : ℕ}
    (eH : Fin p ↪ Fin N) (eJ : Fin n ↪ Fin N)
    (hdisj : ∀ i j, eH i ≠ eJ j) (hh : 0 < h) (hbudget : (d : ℝ)/4 + p ≤ h)
    (u : Euclid n) {σ m R : ℝ} (hσ : 0 < σ)
    (husum : ∑ i, (u i)^2 = σ^2) (hm : m = ∑ i, |u i|)
    (hRdef : R = m^2/σ^2) (hR : 4096 ≤ R) (hRd : R ≤ d)
    (hcap : ∀ i, |u i| ≤ 16*σ/Real.sqrt R) :
    tensorGaussianLaw N h
      {z | spectralNuclearNorm (projectedBilinear
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).1))
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).2))
        n d (selectSample eJ z) u) < projectedConstant * Real.sqrt d * m} ≤
      ENNReal.ofReal (Real.exp (-(d : ℝ)*R/65536)) := by
  let P : GaussianEntries p h × GaussianEntries p h → Euclid h →L[ℝ] Euclid h :=
    fun z => ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h z.1)
  let Q : GaussianEntries p h × GaussianEntries p h → Euclid h →L[ℝ] Euclid h :=
    fun z => ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h z.2)
  let E : Set ((GaussianEntries p h × GaussianEntries p h) ×
      (GaussianEntries n h × GaussianEntries n h)) :=
    {z | spectralNuclearNorm (projectedBilinear (P z.1) (Q z.1) n d z.2 u) <
      projectedConstant * Real.sqrt d * m}
  have hP : Measurable P := measurable_const.sub
    ((measurable_finiteSpanProjector p).comp ((measurable_entriesToRows p h).comp measurable_fst))
  have hQ : Measurable Q := measurable_const.sub
    ((measurable_finiteSpanProjector p).comp ((measurable_entriesToRows p h).comp measurable_snd))
  have hE : MeasurableSet E := measurableSet_lt
    ((continuous_spectralNuclear h h).measurable.comp
      (measurable_projectedBilinear n d hh u P Q hP hQ)) measurable_const
  have hp := disjointSamples_preserving (h := h) eH eJ hdisj
  change tensorGaussianLaw N h (disjointSamples eH eJ ⁻¹' E) ≤ _
  rw [← Measure.map_apply hp.measurable hE, hp.map_eq]
  exact projected_regular_cluster_head_product hh hbudget u hσ husum hm hRdef hR hRd hcap

/-- The same exact original-law estimate for a full coefficient vector supported
on the current indices. The observed matrix is literally B_N(u), without an
assumed replacement by a lower-dimensional sample model. -/
theorem projected_regular_cluster_supported {N p n h d : ℕ}
    (eH : Fin p ↪ Fin N) (eJ : Fin n ↪ Fin N)
    (hdisj : ∀ i j, eH i ≠ eJ j) (hh : 0 < h) (hbudget : (d : ℝ)/4 + p ≤ h)
    (u : Euclid N) (hsupport : ∀ i ∉ Set.range eJ, u i = 0)
    {σ m R : ℝ} (hσ : 0 < σ)
    (husum : ∑ i, (u i)^2 = σ^2) (hm : m = ∑ i, |u i|)
    (hRdef : R = m^2/σ^2) (hR : 4096 ≤ R) (hRd : R ≤ d)
    (hcap : ∀ i, |u i| ≤ 16*σ/Real.sqrt R) :
    tensorGaussianLaw N h
      {z | spectralNuclearNorm (projectedBilinear
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).1))
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).2))
        N d z u) < projectedConstant * Real.sqrt d * m} ≤
      ENNReal.ofReal (Real.exp (-(d : ℝ)*R/65536)) := by
  have hsum : ∑ i, (euclideanCoordinateSubfamily eJ u i)^2 = σ^2 := by
    rw [sum_sq_euclideanCoordinateSubfamily eJ u hsupport, husum]
  have hmass : m = ∑ i, |euclideanCoordinateSubfamily eJ u i| := by
    rw [sum_abs_euclideanCoordinateSubfamily eJ u hsupport, hm]
  have hp := projected_regular_cluster_disjoint_samples eH eJ hdisj hh hbudget
    (euclideanCoordinateSubfamily eJ u) hσ hsum hmass hRdef hR hRd (fun i => hcap (eJ i))
  have heq (z : GaussianEntries N h × GaussianEntries N h) :
      projectedBilinear
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).1))
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).2))
        n d (selectSample eJ z) (euclideanCoordinateSubfamily eJ u) =
      projectedBilinear
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).1))
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).2))
        N d z u := by
    unfold projectedBilinear
    rw [gaussianBilinearOperator_selectSample d eJ z u hsupport]
  simp_rw [heq] at hp
  exact hp

/-- Section 7's logarithmic-cutoff statement, with C_low=8192, c_up=1 and
c_proj=1/(524288√2). This is the actual original Gaussian law and full matrix. -/
theorem projected_regular_cluster_supported_log {N p n h d : ℕ}
    (eH : Fin p ↪ Fin N) (eJ : Fin n ↪ Fin N)
    (hdisj : ∀ i j, eH i ≠ eJ j) (hh : 0 < h) (hd : 2 ≤ d)
    (hbudget : (d : ℝ)/4 + p ≤ h)
    (u : Euclid N) (hsupport : ∀ i ∉ Set.range eJ, u i = 0)
    {σ m R : ℝ} (hσ : 0 < σ)
    (husum : ∑ i, (u i)^2 = σ^2) (hm : m = ∑ i, |u i|)
    (hRdef : R = m^2/σ^2) (hR : 8192 * Real.log d ≤ R) (hRd : R ≤ d)
    (hcap : ∀ i, |u i| ≤ 16*σ/Real.sqrt R) :
    tensorGaussianLaw N h
      {z | spectralNuclearNorm (projectedBilinear
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).1))
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).2))
        N d z u) < projectedConstant * Real.sqrt d * m} ≤
      ENNReal.ofReal (Real.exp (-projectedConstant * (d : ℝ)*R)) := by
  have hR' := regularCluster_log_cutoff hd hR
  apply (projected_regular_cluster_supported eH eJ hdisj hh hbudget u hsupport
    hσ husum hm hRdef hR' hRd hcap).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right projectedConstant_le_exponent
    (mul_nonneg (Nat.cast_nonneg d) (by linarith : 0 ≤ R))
  nlinarith

end GaussianEllipsoid.ProjectedClusters
