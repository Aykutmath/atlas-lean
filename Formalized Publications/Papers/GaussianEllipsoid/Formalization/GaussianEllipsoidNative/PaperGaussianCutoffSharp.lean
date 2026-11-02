import PaperSmoothCutoff
import UCGaussianRowBridge
import PaperProjectedEscapeConcentration
import UCDeletedFrames

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments BMGeometry BMSaddle
namespace UCEscape

/-- Actual-row-law Gaussian good event giving a uniform bounded-loss floor
for all source PSD unit matrices and all nuisance vectors in L. Every analytic,
probability, subspace and normalization input is proved. Remaining premises are
only explicit numerical dimension/gap calibration. -/
theorem exists_gaussian_paper_cutoff_sharp_good_event {n d r k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hr : 0 < r)
    (L : Submodule ℝ (Euclid n)) (hdim : r+Module.finrank ℝ L+k ≤ n)
    (ε a θ ell t : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 < a) (ht : 0 < t)
    (hgap : a*Real.sqrt n < ell) (hθ : θ*(n:ℝ) ≤ (k:ℝ)+1)
    (hmargin : ell+t ≤ (1-ε)*Real.sqrt r*
      (1-((deletedCoordinateSets n k).card:ℝ)*Real.exp (-ε^2*(r:ℝ)/8)) -
        Real.sqrt ((d:ℝ)*(d+1)/4)) :
    ∃ G : Set (BMSaddle.Raw n d), MeasurableSet G ∧
      (BMSaddle.rawSourceLaw n d).real Gᶜ ≤ Real.exp (-t^2/2) ∧
      ∀ z ∈ G, ∀ A : GaussianEllipsoid.Square d, A.PosSemidef → frobeniusNorm A = 1 →
        ∀ v : Euclid n, v ∈ L →
          θ ≤
            (∑ i, PaperSmoothCutoff.loss a
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
  let G : Set (BMSaddle.Raw n d) := {z | ell ≤ projectedEscape (d := d) U (rawSample n d z)}
  have hmeas : Measurable (fun z => projectedEscape (d := d) U (rawSample n d z)) :=
    (projectedEscape_lipschitz hd U).continuous.measurable.comp (rawSample_preserving n d).measurable
  refine ⟨G, measurableSet_le measurable_const hmeas, ?_, ?_⟩
  · have he : Gᶜ = {z | rawSample n d z ∈ {X | projectedEscape (d := d) U X < ell}} := by
      ext z
      simp only [G, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [he, gaussianRows_event n d _
      (measurableSet_lt (projectedEscape_lipschitz hd U).continuous.measurable measurable_const)]
    have hm : ell ≤ (1-ε)*Real.sqrt r*
        (1-(Fintype.card J:ℝ)*Real.exp (-ε^2*(r:ℝ)/8)) -
        Real.sqrt ((d:ℝ)*(d+1)/4)-t := by
      have hm := hmargin
      dsimp only [J] at ⊢
      simp only [Fintype.card_coe] at ⊢
      linarith
    exact (measureReal_mono (fun X hX => hX.trans_le hm)).trans
      (projectedEscape_explicit_sharp_lower_tail hd hr U ε hε hε1 t ht.le)
  · intro z hz A hA hF v hv
    have hc := many_large_residual_coordinates_of_projectedEscape L U horth hsupp
      (rawSample n d z) (sourceFrobenius A) (sourceFrobenius_mem_psdUnit A hA hF)
      v hv a (le_of_lt ha) (hgap.trans_le hz)
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have hcard : θ*(n:ℝ) ≤
        ((largeResidualCoordinates (measurement (rawSample n d z) (sourceFrobenius A)) v a).card : ℝ) := by
      have hnat : k+1 ≤ (largeResidualCoordinates
        (measurement (rawSample n d z) (sourceFrobenius A)) v a).card := hc
      have hreal : (k:ℝ)+1 ≤ ((largeResidualCoordinates
        (measurement (rawSample n d z) (sourceFrobenius A)) v a).card : ℝ) := by exact_mod_cast hnat
      exact hθ.trans hreal
    have h := ((le_div_iff₀ hn').2 hcard).trans
      (PaperSmoothCutoff.average_ge_fraction hn ha
        (fun i => measurement (rawSample n d z) (sourceFrobenius A) i - v i))
    simp_rw [← gaussianRow_eq_measurement] at h
    exact h

#print axioms exists_gaussian_paper_cutoff_sharp_good_event
end UCEscape
