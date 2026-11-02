import UCDiffuseUnbounded
import UCHeadNuisance
import UCPeeledDimension

/-! Uniform actual probabilities for every deterministic fixed head/tail
splitting, before choosing a finite frame net. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Module
open scoped BigOperators Topology
namespace GaussianEllipsoid.UCFrameProbability
open UCDiffuseUnbounded UCDiffuseFiniteModel

 def fixedSplitBad {d j p n : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin p))
    (τ c : ℝ) : Set (Sample d n) :=
  {x | UCEscape.gaussianSampleBlockSplit e n x ∈
    UCEscape.headTailQuadraticBadEvent (sourceDiffuseClass p τ) c}

 theorem measurableSet_fixedSplitBad {d j p n : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin p))
    (τ c : ℝ) : MeasurableSet (fixedSplitBad (n := n) e τ c) :=
  (UCEscape.headTailQuadraticBadEvent_isOpen (sourceDiffuseClass p τ) c).measurableSet.preimage
    (UCEscape.gaussianSampleBlockSplit_preserving e n).measurable

/-- Constants precede the peeling budget K. Each actual fixed splitting then
has an exponentially small failure probability at the original d² scale. -/
theorem exists_uniform_fixed_split_tail (αm αp : ℝ) (hαm : 1/4 < αm) (hαp : αm ≤ αp) :
    ∃ τ c C : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ K : ℕ, ∀ᶠ d : ℕ in atTop, ∀ n : ℕ,
        αm*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ αp*(d:ℝ)^2 →
        ∀ j : ℕ, j ≤ K →
          ∀ e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin (d-j)),
            (gaussianSampleLaw d n).real (fixedSplitBad e τ c) ≤ Real.exp (-C*(d:ℝ)^2) := by
  have hαm0 : 0 < αm := by linarith
  have hαp0 : 0 < αp := by linarith
  have hαp' : αm ≤ 4*αp := by linarith
  obtain ⟨τ,c,C,hτ,hτ1,hc,hC,hTail⟩ := uniform_diffuse_unbounded αm (4*αp) hαm hαp'
  refine ⟨τ,c,C/4,hτ,hτ1,hc,by positivity,?_⟩
  intro K
  obtain ⟨D,hD⟩ := eventually_atTop.mp (hTail (1+K^2))
  filter_upwards [eventually_ge_atTop (D+K),eventually_ge_atTop (2*K),eventually_ge_atTop 1] with d hdD hdK hd1
  intro n hnlo hnhi j hj e
  have hdpos : 0 < d := by omega
  have hpD : D ≤ d-j := by omega
  have haspect := UCEscape.peeled_aspect_bounds n d K j αm αp hdpos hdK hj hαm0.le hαp0.le hnlo hnhi
  have hbound : ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), finrank ℝ L ≤ 1+j^2 →
      (gaussianSampleLaw (d-j) n).real
        {t | ∃ A : sourceDiffuseClass (d-j) τ, ∃ v : EuclideanSpace ℝ (Fin n), v ∈ L ∧
          (∑ i, |measurementQ t A.val i-v i|)/(n:ℝ) < c} ≤ Real.exp (-C*((d-j:ℕ):ℝ)^2) := by
    intro L hL
    have hLK : finrank ℝ L ≤ 1+K^2 := hL.trans (by nlinarith)
    have ht := hD (d-j) hpD n haspect.1 haspect.2 L hLK
    have hsub : {t : Sample (d-j) n | ∃ A : sourceDiffuseClass (d-j) τ,
        ∃ v : EuclideanSpace ℝ (Fin n), v ∈ L ∧ (∑ i, |measurementQ t A.val i-v i|)/(n:ℝ) < c} ⊆
        uncappedDiffuseBad (d-j) n τ c L := by
      rintro x ⟨⟨A,hA⟩,v,hv,hbad⟩
      refine ⟨A,hA,v,hv,?_⟩
      simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using hbad
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans ht
  have h := UCEscape.gaussian_head_conditioning_transfer e (sourceDiffuseClass (d-j) τ) c
    (Real.exp (-C*((d-j:ℕ):ℝ)^2)) (Real.exp_nonneg _) hbound
  exact h.trans (UCEscape.peeled_exponential_bound d K j C hdpos hdK hj hC.le)

#print axioms exists_uniform_fixed_split_tail
end GaussianEllipsoid.UCFrameProbability
