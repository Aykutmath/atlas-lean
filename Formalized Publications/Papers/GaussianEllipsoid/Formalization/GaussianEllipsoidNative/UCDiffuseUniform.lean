import UCDiffuseActualBound
import UCGaussianAspectCalibration

/-! Unconditional, quantitative diffuse conic lower bound on every fixed
aspect interval above 1/4. The margin, cap, and failure exponent are all
independent of the fixed nuisance rank and nuisance-radius constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Module BMClippedL1Bridge
open scoped Topology
namespace GaussianEllipsoid.UCDiffuseUniform
open UCDiffuseActualBound UCDiffuseParameters UCDiffuseNets

/-- All Gaussian, universality, entropy, net, and concentration inputs are
fully discharged. This is the actual bounded-nuisance diffuse theorem. -/
theorem uniform_diffuse_bound (αm αp : ℝ) (hαm : 1/4 < αm) (hαp : αm ≤ αp) :
    ∃ τ c C : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ M : ℕ, ∀ B : ℝ, 0 ≤ B → ∀ᶠ d : ℕ in atTop, ∀ n : ℕ,
        αm*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ αp*(d:ℝ)^2 →
        ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), finrank ℝ L ≤ M →
          (gaussianSampleLaw d n).real (diffuseBad d n τ B c L) ≤ Real.exp (-C*(d:ℝ)^2) := by
  obtain ⟨a,θ,cg,ha,hθ,hcg,hGaussian⟩ :=
    UCEscape.exists_uniform_aspect_gaussian_loss_good_event αm αp hαm hαp
  let η := θ*smoothLoss a
  have hη : 0 < η := mul_pos hθ (smoothLoss_pos ha)
  obtain ⟨r,s,β,τ,hr,hs,hβ,hτ,hτ1,hmesh,hβEnt,hsmall⟩ := exists_parameters η hη
  obtain ⟨C,hC,hExp⟩ := exponential_pair_eventually η hη
  refine ⟨τ,η/2,C,hτ,hτ1,by positivity,hC,?_⟩
  intro M B hB
  obtain ⟨DG,hDG⟩ := hGaussian M (1/16) (by norm_num)
  have hNEnt := eventually_forall_quarter_square (nuisance_entropy_eventually M B s hB hs)
  filter_upwards [hNEnt,hExp,eventually_ge_atTop DG,eventually_ge_atTop 1] with d hdEnt hdExp hdG hd1
  intro n hnlo hnhi L hL
  have hd : 0 < d := by omega
  have hquarter : (1/4:ℝ)*(d:ℝ)^2 ≤ n :=
    (mul_le_mul_of_nonneg_right hαm.le (sq_nonneg (d:ℝ))).trans hnlo
  have hnR : (0:ℝ) < n := by
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_pos_of_pos hdR]
  have hn : 0 < n := by exact_mod_cast hnR
  obtain ⟨G,hG,_,hp,hfloor⟩ := hDG d hdG n hnlo hnhi L hL
  have hb := diffuse_tail_of_gaussian_good_event hd hn hquarter L hL B η r s β τ hB hη
    hr hs hβ hτ.le hmesh hβEnt (hsmall hβ.le) (hdEnt n hquarter) G hG hp hfloor
  exact hb.trans (hdExp n hquarter)

#print axioms uniform_diffuse_bound
end GaussianEllipsoid.UCDiffuseUniform
