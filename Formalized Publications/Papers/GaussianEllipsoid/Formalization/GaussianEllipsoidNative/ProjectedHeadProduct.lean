import ProjectedRegularCluster
import FiniteSpanProjector
import GaussianDisjointSamples

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Module
open GaussianMixedNormHelpers GaussianTensorMoments GaussianPairedBlocks
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoid.ProjectedClusters

/-- A measurable external parameter may choose the residual projections.
Pointwise bases are used only inside the fixed-fibre proof; no measurable
choice of orthonormal bases is assumed. -/
theorem projected_regular_cluster_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n h d : ℕ} (hh : 0 < h)
    (W Z : Ω → Submodule ℝ (Euclid h))
    (hWm : Measurable (fun ω => (W ω).subtypeL ∘L (W ω).orthogonalProjection))
    (hZm : Measurable (fun ω => (Z ω).subtypeL ∘L (Z ω).orthogonalProjection))
    (hrank : ∀ᵐ ω ∂μ, (d : ℝ)/4 ≤ finrank ℝ (W ω) ∧ (d : ℝ)/4 ≤ finrank ℝ (Z ω))
    (u : Euclid n) {σ m R : ℝ} (hσ : 0 < σ)
    (husum : ∑ i, (u i)^2 = σ^2) (hm : m = ∑ i, |u i|)
    (hRdef : R = m^2/σ^2) (hR : 4096 ≤ R) (hRd : R ≤ d)
    (hcap : ∀ i, |u i| ≤ 16*σ/Real.sqrt R) :
    (μ.prod (tensorGaussianLaw n h))
      {p | spectralNuclearNorm (projectedBilinear
        ((W p.1).subtypeL ∘L (W p.1).orthogonalProjection)
        ((Z p.1).subtypeL ∘L (Z p.1).orthogonalProjection) n d p.2 u) <
          projectedConstant * Real.sqrt d * m} ≤
      ENNReal.ofReal (Real.exp (-(d : ℝ)*R/65536)) := by
  have hS : MeasurableSet {p : Ω × (GaussianEntries n h × GaussianEntries n h) |
      spectralNuclearNorm (projectedBilinear
        ((W p.1).subtypeL ∘L (W p.1).orthogonalProjection)
        ((Z p.1).subtypeL ∘L (Z p.1).orthogonalProjection) n d p.2 u) <
          projectedConstant * Real.sqrt d * m} :=
    measurableSet_lt ((continuous_spectralNuclear h h).measurable.comp
      (measurable_projectedBilinear n d hh u
        (fun ω => (W ω).subtypeL ∘L (W ω).orthogonalProjection)
        (fun ω => (Z ω).subtypeL ∘L (Z ω).orthogonalProjection) hWm hZm)) measurable_const
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (Real.exp (-(d : ℝ)*R/65536)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hrank] with ω hω
      exact projected_regular_cluster (W ω) (Z ω) hω.1 hω.2 u hσ husum hm hRdef hR hRd hcap
    _ = _ := by simp

/-- The actual residual space after removing a finite family. -/
def headResidual {h p : ℕ} (a : Fin p → Euclid h) : Submodule ℝ (Euclid h) :=
  (Submodule.span ℝ (Set.range a))ᗮ

/-- The residual projector is the identity minus the actual finite-span projector. -/
theorem headResidual_projector {h p : ℕ} (a : Fin p → Euclid h) :
    (headResidual a).subtypeL ∘L (headResidual a).orthogonalProjection =
      ContinuousLinearMap.id ℝ _ - finiteSpanProjector a := by
  apply ContinuousLinearMap.ext
  intro x
  exact Submodule.starProjection_orthogonal_val _

theorem measurable_headResidual_projector (h p : ℕ) :
    Measurable (fun a : Fin p → Euclid h =>
      (headResidual a).subtypeL ∘L (headResidual a).orthogonalProjection) := by
  simp_rw [headResidual_projector]
  exact measurable_const.sub (measurable_finiteSpanProjector p)

/-- Rank loss is at most the number of removed samples, even at all rank drops. -/
theorem headResidual_rank_loss {h p : ℕ} (a : Fin p → Euclid h) :
    h ≤ p + finrank ℝ (headResidual a) := by
  have hr := finrank_range_le_card (R := ℝ) a
  have hs := (Submodule.span ℝ (Set.range a)).finrank_add_finrank_orthogonal
  simp only [Fintype.card_fin] at hr
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hs
  change h ≤ p + finrank ℝ (Submodule.span ℝ (Set.range a))ᗮ
  change finrank ℝ (Submodule.span ℝ (Set.range a)) ≤ p at hr
  omega

/-- Actual head-conditioned product bound, with finite-span Borel projectors
and deterministic rank loss both proved rather than assumed. -/
theorem projected_regular_cluster_head_product {p n h d : ℕ}
    (hh : 0 < h) (hbudget : (d : ℝ)/4 + p ≤ h)
    (u : Euclid n) {σ m R : ℝ} (hσ : 0 < σ)
    (husum : ∑ i, (u i)^2 = σ^2) (hm : m = ∑ i, |u i|)
    (hRdef : R = m^2/σ^2) (hR : 4096 ≤ R) (hRd : R ≤ d)
    (hcap : ∀ i, |u i| ≤ 16*σ/Real.sqrt R) :
    ((tensorGaussianLaw p h).prod (tensorGaussianLaw n h))
      {z | spectralNuclearNorm (projectedBilinear
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h z.1.1))
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h z.1.2))
        n d z.2 u) < projectedConstant * Real.sqrt d * m} ≤
      ENNReal.ofReal (Real.exp (-(d : ℝ)*R/65536)) := by
  have hW : Measurable (fun z : GaussianEntries p h × GaussianEntries p h =>
      (headResidual (entriesToRows p h z.1)).subtypeL ∘L
        (headResidual (entriesToRows p h z.1)).orthogonalProjection) :=
    (measurable_headResidual_projector h p).comp
    ((measurable_entriesToRows p h).comp measurable_fst)
  have hZ : Measurable (fun z : GaussianEntries p h × GaussianEntries p h =>
      (headResidual (entriesToRows p h z.2)).subtypeL ∘L
        (headResidual (entriesToRows p h z.2)).orthogonalProjection) :=
    (measurable_headResidual_projector h p).comp
    ((measurable_entriesToRows p h).comp measurable_snd)
  have hrank : ∀ᵐ z ∂tensorGaussianLaw p h,
      (d : ℝ)/4 ≤ finrank ℝ (headResidual (entriesToRows p h z.1)) ∧
      (d : ℝ)/4 ≤ finrank ℝ (headResidual (entriesToRows p h z.2)) := by
    apply Filter.Eventually.of_forall
    intro z
    constructor
    · have hr : (h : ℝ) ≤ p + finrank ℝ (headResidual (entriesToRows p h z.1)) :=
        by exact_mod_cast headResidual_rank_loss (entriesToRows p h z.1)
      linarith
    · have hr : (h : ℝ) ≤ p + finrank ℝ (headResidual (entriesToRows p h z.2)) :=
        by exact_mod_cast headResidual_rank_loss (entriesToRows p h z.2)
      linarith
  simpa only [headResidual_projector] using
    projected_regular_cluster_product (tensorGaussianLaw p h) hh
      (fun z => headResidual (entriesToRows p h z.1))
      (fun z => headResidual (entriesToRows p h z.2))
      hW hZ hrank u hσ husum hm hRdef hR hRd hcap

end GaussianEllipsoid.ProjectedClusters
