import PaperDiffuseActualBound
import PaperGrowingRankGaussian

/-! Quantitative diffuse conic lower bound on every effective aspect interval
above 1/4. Constants may depend on the l1 radius B. The dimension cutoff is
uniform over all nuisance dimensions allowed by the effective aspect bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Module BMClippedL1Bridge
open scoped Topology
namespace GaussianEllipsoid.PaperDiffuseUniform
open PaperDiffuseActualBound UCDiffuseParameters UCDiffuseNets

/-- All Gaussian, universality, entropy, net, and concentration inputs are
fully discharged. This is the actual bounded-nuisance diffuse theorem. -/
theorem uniform_diffuse_bound (αm αp B : ℝ) (hαm : 1/4 < αm) (hαp : αm ≤ αp) (hB : 0 ≤ B) :
    ∃ τ c C : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, (n:ℝ) ≤ αp*(d:ℝ)^2 →
        ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
        αm*(d:ℝ)^2 ≤ (n:ℝ)-(finrank ℝ L:ℝ) →
          (gaussianSampleLaw d n).real (diffuseBad d n τ B c L) ≤ Real.exp (-C*(d:ℝ)^2) := by
  obtain ⟨a,θ,cg,ha,hθ,hcg,hGaussian⟩ :=
    UCEscape.exists_effective_aspect_gaussian_loss_good_event αm αp hαm hαp
  let η := θ*smoothLoss a
  have hη : 0 < η := mul_pos hθ (smoothLoss_pos ha)
  obtain ⟨r,s,β,τ,hr,hs,hβ,hτ,hτ1,hmesh,hβEnt,hsmall⟩ := PaperL1Entropy.exists_parameters η B hη hB
  obtain ⟨C,hC,hExp⟩ := exponential_pair_eventually η hη
  refine ⟨τ,η/2,C,hτ,hτ1,by positivity,hC,?_⟩
  obtain ⟨DG,hDG⟩ := hGaussian (1/16) (by norm_num)
  filter_upwards [hExp,eventually_ge_atTop DG,eventually_ge_atTop 1] with d hdExp hdG hd1
  intro n hnhi L heffective
  have hnlo : αm*(d:ℝ)^2 ≤ n := heffective.trans (sub_le_self _ (Nat.cast_nonneg (finrank ℝ L)))
  have hd : 0 < d := by omega
  have hquarter : (1/4:ℝ)*(d:ℝ)^2 ≤ n :=
    (mul_le_mul_of_nonneg_right hαm.le (sq_nonneg (d:ℝ))).trans hnlo
  have hnR : (0:ℝ) < n := by
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_pos_of_pos hdR]
  have hn : 0 < n := by exact_mod_cast hnR
  obtain ⟨G,hG,_,hp,hfloor⟩ := hDG d hdG n hnhi L heffective
  have hb := diffuse_tail_of_gaussian_good_event hd hn hquarter L B η r s β τ hB hη
    hr hs hβ hτ.le hmesh hβEnt (hsmall hβ.le) G hG hp hfloor
  exact hb.trans (hdExp n hquarter)

#print axioms uniform_diffuse_bound
end GaussianEllipsoid.PaperDiffuseUniform
