import UCGaussianRowBridge
import UCEscapeProbability
import UCDeletedFrames

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments BMGeometry BMSaddle
namespace UCEscape

/-- Actual-row-law Gaussian good event giving a uniform bounded-loss floor
for all source PSD unit matrices and all nuisance vectors in L. Every analytic,
probability, subspace and normalization input is proved. Remaining premises are
only explicit numerical dimension/gap calibration. -/
theorem exists_gaussian_loss_good_event {n d r k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hr : 0 < r)
    (L : Submodule ℝ (Euclid n)) (hdim : r+Module.finrank ℝ L+k ≤ n)
    (ε a θ ell t : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a) (ht : 0 < t)
    (hgap : a*Real.sqrt n < ell) (hθ : θ*(n:ℝ) ≤ (k:ℝ)+1)
    (hmargin : ell+t ≤ (1-ε)*Real.sqrt r*
      (1-((deletedCoordinateSets n k).card:ℝ)*Real.exp (-ε^2*(r:ℝ)/8)) -
        Real.sqrt ((d:ℝ)*(d+1)/4)) :
    ∃ G : Set (BMSaddle.Raw n d), MeasurableSet G ∧
      (BMSaddle.rawSourceLaw n d).real Gᶜ ≤ Real.pi^2/(8*t^2) ∧
      ∀ z ∈ G, ∀ A : GaussianEllipsoid.Square d, A.PosSemidef → frobeniusNorm A = 1 →
        ∀ v : Euclid n, v ∈ L →
          θ*BMClippedL1Bridge.smoothLoss a ≤
            (∑ i, BMClippedL1Bridge.smoothLoss
              (GaussianEllipsoid.UCNormalizedRows.gaussianRow A (z i)-v i))/(n:ℝ) := by
  classical
  let J := ↥(deletedCoordinateSets n k)
  let f : J → ℝ := fun j => ((Fintype.equivFin J j).val : ℝ)
  have hf : Function.Injective f := by
    intro i j h
    apply (Fintype.equivFin J).injective
    apply Fin.ext
    dsimp [f] at h
    exact_mod_cast h
  letI : MetricSpace J := MetricSpace.induced f hf inferInstance
  letI : DiscreteTopology J := inferInstance
  obtain ⟨U,horth,hsupp⟩ := exists_deleted_frame_family L hdim
  let G : Set (BMSaddle.Raw n d) := {z | ell < projectedEscape (d := d) U (rawSample n d z)}
  have hmeas : Measurable (fun z => projectedEscape (d := d) U (rawSample n d z)) :=
    (projectedEscape_lipschitz hd U).continuous.measurable.comp (rawSample_preserving n d).measurable
  refine ⟨G, measurableSet_lt measurable_const hmeas, ?_, ?_⟩
  · have he : Gᶜ = {z | rawSample n d z ∈ {X | projectedEscape (d := d) U X ≤ ell}} := by
      ext z
      simp only [G, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    rw [he, gaussianRows_event n d _
      (measurableSet_le (projectedEscape_lipschitz hd U).continuous.measurable measurable_const)]
    apply projectedEscape_lower_tail hd hr U ε hε hε1 ell t ht
    simpa only [Fintype.card_coe] using hmargin
  · intro z hz A hA hF v hv
    have h := smoothLoss_average_lower_of_projectedEscape hn L U horth hsupp
      (rawSample n d z) (sourceFrobenius A) (sourceFrobenius_mem_psdUnit A hA hF)
      v hv a θ ha (hgap.trans hz) hθ
    simp_rw [← gaussianRow_eq_measurement] at h
    exact h

#print axioms exists_gaussian_loss_good_event
end UCEscape
