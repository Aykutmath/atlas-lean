import RealDeterminantSymmetry
import RealDeterminantExtended
import CappedVertexPermutation

noncomputable section
open MeasureTheory Finset Filter
open scoped Topology
namespace GaussianEllipsoid.CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Real-exponent, arbitrary-cap regularized extremization against any fixed
capped vertex. No integrability, matrix convexity, or symmetry assumption is
left to the caller. -/
theorem regularizedRealMoment_le_capped_vertex
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {a ε s : ℝ} (ha : 0 < a) (hε : 0 < ε) (hs : 0 ≤ s)
    {w v : κ → ℝ} (hw : w ∈ slice a 1) (hv : v ∈ slice a 1)
    (hvc : (interior a v).card ≤ 1) :
    regularizedRealMoment (Measure.pi (fun _ : κ => μ)) ε s w ≤
      regularizedRealMoment (Measure.pi (fun _ : κ => μ)) ε s v := by
  obtain ⟨u, hu, hle, huc⟩ := exists_almost_vertex_ge_of_pairwise a 1
    (regularizedRealMoment (Measure.pi (fun _ : κ => μ)) ε s)
    (pairwiseConvex_regularizedRealMoment _ hε a 1 s hs) hw
  obtain ⟨e, he⟩ := almost_vertex_perm ha hu hv huc hvc
  rw [he, regularizedRealMoment_perm μ ε s v e] at hle
  exact hle

/-- Paper Lemma 5.1 at arbitrary real exponent and cap. The extremizer is
specified up to permutation by its defining capped-slice and single-remainder
conditions; `almost_vertex_cap_remainder` proves the exact floor and remainder.
Singular determinants contribute infinity. This holds for every iid vector
law, and therefore in particular for the Gaussian law in the paper. -/
theorem extendedRealMoment_le_capped_vertex
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    {w v : κ → ℝ} (hw : w ∈ slice a 1) (hv : v ∈ slice a 1)
    (hvc : (interior a v).card ≤ 1) :
    extendedRealMoment (Measure.pi (fun _ : κ => μ)) s w ≤
      extendedRealMoment (Measure.pi (fun _ : κ => μ)) s v := by
  apply le_of_tendsto_of_tendsto
    (tendsto_ofReal_regularizedRealMoment _ (fun i => (hw.1 i).1) s hs.le)
    (tendsto_ofReal_regularizedRealMoment _ (fun i => (hv.1 i).1) s hs.le)
  filter_upwards [] with n
  exact ENNReal.ofReal_le_ofReal
    (regularizedRealMoment_le_capped_vertex μ ha (ridgeSeq_pos n) hs.le hw hv hvc)
/-- A single exact floor/remainder extremizer works simultaneously for every
admissible weight vector and every positive real exponent. Its ordering is
irrelevant by the proved iid permutation identity. -/
theorem exists_exact_capped_extremizer
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a) (hfeas : (slice (ι := κ) a 1).Nonempty) :
    ∃ v ∈ slice a 1,
      (Finset.univ.filter (fun i => v i = a)).card = Nat.floor (1/a) ∧
      (interior a v).card ≤ 1 ∧
      (∀ i, v i = 0 ∨ v i = a ∨ v i = 1 - (Nat.floor (1/a):ℝ)*a) ∧
      ∀ w ∈ slice a 1, ∀ s : ℝ, 0 < s →
        extendedRealMoment (Measure.pi (fun _ : κ => μ)) s w ≤
          extendedRealMoment (Measure.pi (fun _ : κ => μ)) s v := by
  obtain ⟨w, hw⟩ := hfeas
  obtain ⟨v, hv, _, hvc⟩ := exists_almost_vertex_ge_of_pairwise a 1
    (regularizedRealMoment (Measure.pi (fun _ : κ => μ)) 1 0)
    (pairwiseConvex_regularizedRealMoment _ (by norm_num) a 1 0 (by norm_num)) hw
  have hshape := almost_vertex_cap_remainder ha hv hvc
  exact ⟨v, hv, hshape.1, hvc, hshape.2,
    fun u hu s hs => extendedRealMoment_le_capped_vertex μ ha hs hu hv hvc⟩

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.extendedRealMoment_le_capped_vertex
