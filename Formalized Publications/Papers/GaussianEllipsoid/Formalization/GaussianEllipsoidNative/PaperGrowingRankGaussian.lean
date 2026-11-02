import PaperGrowingRankCalibration

noncomputable section
open MeasureTheory ProbabilityTheory
namespace UCEscape

/-- Gaussian bounded-loss floor with nuisance rank permitted to grow with dimension. -/
theorem exists_effective_aspect_gaussian_loss_good_event (αm αp : ℝ)
    (hαm : 1 / 4 < αm) (hαp : αm ≤ αp) :
    ∃ a θ c : ℝ, 0 < a ∧ 0 < θ ∧ 0 < c ∧
      ∀ q : ℝ, 0 < q → ∃ D : ℕ,
        ∀ d ≥ D, ∀ n : ℕ,
          (n : ℝ) ≤ αp * (d : ℝ)^2 →
          ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
          αm * (d : ℝ)^2 ≤ (n:ℝ)-(Module.finrank ℝ L:ℝ) →
          ∃ G : Set (BMSaddle.Raw n d), MeasurableSet G ∧
            (BMSaddle.rawSourceLaw n d).real Gᶜ ≤ Real.pi^2 / (8 * (c * d)^2) ∧
            (BMSaddle.rawSourceLaw n d).real Gᶜ ≤ q ∧
            ∀ z ∈ G, ∀ A : GaussianEllipsoid.Square d,
              A.PosSemidef → GaussianEllipsoid.frobeniusNorm A = 1 →
              ∀ v : EuclideanSpace ℝ (Fin n), v ∈ L →
                θ * BMClippedL1Bridge.smoothLoss a ≤
                  (∑ i, BMClippedL1Bridge.smoothLoss
                    (GaussianEllipsoid.UCNormalizedRows.gaussianRow A (z i) - v i)) / (n : ℝ) := by
  obtain ⟨β, ε, c, θ, hβ, hβα, hε, hεhalf, hc, hθ, hθ1, hmargin, hslack, hent⟩ :=
    exists_aspect_escape_constants αm αp hαm hαp
  have hαm0 : 0 < αm := by linarith
  have hαp0 : 0 < αp := by linarith
  have hβ0 : 0 < β := by linarith
  let a := c / (2 * Real.sqrt αp)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, θ, c, ha, hθ, hc, ?_⟩
  intro q hq
  obtain ⟨D, hD⟩ := effective_aspect_numeric_calibration_eventually αm αp β ε c θ hαm0 hαp0 hβ0
    hε hεhalf hc hθ hθ1 hmargin hslack hent q hq
  refine ⟨D, ?_⟩
  intro d hd n hnhi L hnlo
  obtain ⟨hnpos, hdpos, hrpos, hdim, hθk, hgap, hmean, hprob⟩ := hD d hd n (Module.finrank ℝ L) hnlo hnhi
  let k := Nat.floor (θ * n)
  let r := n - Module.finrank ℝ L - k
  have hdimL : r + Module.finrank ℝ L + k ≤ n := by dsimp [r, k]; omega
  obtain ⟨G, hG, htail, hfloor⟩ := exists_gaussian_loss_good_event (r := r) (k := k)
    hnpos hdpos hrpos L hdimL ε a θ (c * d) (c * d) hε.le (by linarith) ha.le
    (mul_pos hc (Nat.cast_pos.mpr hdpos)) hgap hθk hmean
  exact ⟨G, hG, htail, htail.trans hprob, hfloor⟩

#print axioms exists_effective_aspect_gaussian_loss_good_event
end UCEscape
