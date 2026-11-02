import GaussianLocalizedDecay
import GaussianLocalizedMeasurability
import BilinearLawTransport
import GaussianBilinearMeasurability

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianEllipsoid.SmallBall
open GaussianBilinearTransport GaussianTensorMoments Filter
open scoped Topology

namespace GaussianEllipsoid.Localized

/-- Exact observation identity in the inverse sample-law direction. -/
theorem localizedOperator_smallBallToFlat (n r d : ℕ) (hr : 0 < r)
    (p : BilinearSample r n) (x : Coeff n) :
    localizedOperator d r n p x =
      gaussianBilinearOperator n r d (smallBallToFlat n r p) x := by
  have h := bilinearScaled_flatToSmallBall n r d hr (smallBallToFlat n r p) x
  rw [flatToSmallBall_smallBallToFlat] at h
  exact h

/-- Actual continuity exceptional probability under the identical small-ball
sample law. The change of representation is measure-preserving, not assumed. -/
theorem gaussian_localized_continuity_compl_le (n r d : ℕ)
    (hd : 0 < d) (hr : 0 < r) (hrd : r ≤ d) (hn : n ≤ d^2) :
    (bilinearGaussianSampleLaw r n).real
      (frobeniusContinuity (localizedOperator d r n) 96 d)ᶜ ≤
      (r:ℝ)^2/(2:ℝ)^r := by
  let S := {z | 96*Real.sqrt (d:ℝ) < ‖gaussianBilinearOperator n r d z‖}
  have hsub : (frobeniusContinuity (localizedOperator d r n) 96 d)ᶜ ⊆
      (smallBallToFlat n r) ⁻¹' S := by
    intro p hp
    change 96*Real.sqrt (d:ℝ) < ‖gaussianBilinearOperator n r d (smallBallToFlat n r p)‖
    by_contra hnot
    have hnorm := le_of_not_gt hnot
    apply hp
    intro x
    rw [localizedOperator_smallBallToFlat n r d hr]
    exact (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg x))
  calc
    _ ≤ (bilinearGaussianSampleLaw r n).real ((smallBallToFlat n r) ⁻¹' S) :=
      measureReal_mono hsub
    _ = (tensorGaussianLaw n r).real S :=
      (smallBallToFlat_preserving n r).measureReal_preimage
        (gaussianBilinearOperator_bad_measurableSet n r d 96).nullMeasurableSet
    _ ≤ _ := gaussianBilinearOperator_norm_tail n r d hd hr hrd hn

/-- Remove the continuity intersection with the actual quantitative L=96 bound.
Every term is now under the original independent Gaussian law. -/
theorem gaussian_localized_unconditional_probability {α A B β K : ℝ} {d n : ℕ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K)
    (hd : max 12 (entropyCutoff α A B β K 96) ≤ d)
    (hn : (n:ℝ) ≤ α*(d:ℝ)^2) :
    (bilinearGaussianSampleLaw (2*(d/4)) n).real
      (homogeneousBad (localizedOperator d (2*(d/4)) n)
        A β B K (entropyScale α B β 96) d) ≤
      Real.exp (-(d:ℝ)^2) + ((2*(d/4):ℕ):ℝ)^2/(2:ℝ)^(2*(d/4)) := by
  let T := localizedOperator (d:ℝ) (2*(d/4)) n
  let F := homogeneousBad T A β B K (entropyScale α B β 96) d
  let E := frobeniusContinuity T 96 d
  have hsub : F ⊆ (F ∩ E) ∪ Eᶜ := by
    intro p hp
    by_cases he : p ∈ E
    · exact Or.inl ⟨hp,he⟩
    · exact Or.inr he
  have hd12 : 12 ≤ d := (le_max_left _ _).trans hd
  have hn' : n ≤ d^2 := by
    have hh : (n:ℝ) ≤ (d:ℝ)^2 := hn.trans
      (mul_le_of_le_one_left (sq_nonneg _) (by linarith : α ≤ 1))
    exact_mod_cast hh
  have hE := gaussian_localized_continuity_compl_le n (2*(d/4)) d
    (by omega) (by omega) (by omega) hn'
  calc
    _ ≤ (bilinearGaussianSampleLaw (2*(d/4)) n).real ((F ∩ E) ∪ Eᶜ) :=
      measureReal_mono hsub
    _ ≤ (bilinearGaussianSampleLaw (2*(d/4)) n).real (F ∩ E) +
        (bilinearGaussianSampleLaw (2*(d/4)) n).real Eᶜ := measureReal_union_le _ _
    _ ≤ _ := add_le_add
      (gaussian_localized_exp_decay hα hα' hA hB hβ hK (by norm_num) hd hn) hE

/-- The full, unintersected bad-event probability tends to zero at every
strictly subcritical aspect ratio. No abstract continuity premise remains. -/
theorem gaussian_localized_bad_probability_tendsto_zero {α A B β K : ℝ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K) (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, (n d:ℝ) ≤ α*(d:ℝ)^2) :
    Tendsto (fun d => (bilinearGaussianSampleLaw (2*(d/4)) (n d)).real
      (homogeneousBad (localizedOperator d (2*(d/4)) (n d))
        A β B K (entropyScale α B β 96) d)) atTop (𝓝 0) := by
  have hExp : Tendsto (fun d : ℕ => Real.exp (-(d:ℝ)^2)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hdim : Tendsto (fun d : ℕ => 2*(d/4)) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop (4*M)] with d hd
    omega
  have hError := tensor_covariance_error_tendsto_zero.comp hdim
  have hUpper := hExp.add hError
  simp only [zero_add] at hUpper
  apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _ hUpper
  filter_upwards [hn, eventually_ge_atTop (max 12 (entropyCutoff α A B β K 96))]
    with d hnd hd
  exact gaussian_localized_unconditional_probability hα hα' hA hB hβ hK hd hnd

/-- A fixed positive small-coordinate scale makes the complete bad event
asymptotically negligible, using only the original numerical parameters. -/
theorem exists_gaussian_localized_bad_probability_tendsto_zero {α A B β K : ℝ}
    (hα : 0 < α) (hα' : α < 1/4) (hA : 0 < A) (hB : 0 < B)
    (hβ : 0 < β) (hK : 0 < K) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n : ℕ → ℕ,
      (∀ᶠ d in atTop, (n d:ℝ) ≤ α*(d:ℝ)^2) →
      Tendsto (fun d => (bilinearGaussianSampleLaw (2*(d/4)) (n d)).real
        (homogeneousBad (localizedOperator d (2*(d/4)) (n d)) A β B K c d))
        atTop (𝓝 0) := by
  obtain ⟨_,_,_,hc,hc1,_⟩ := entropy_constants hα hα' hA hB hβ (by norm_num : (0:ℝ) < 96)
  exact ⟨entropyScale α B β 96,hc,hc1,fun n hn =>
    gaussian_localized_bad_probability_tendsto_zero hα hα' hA hB hβ hK n hn⟩

end GaussianEllipsoid.Localized

#print axioms GaussianEllipsoid.Localized.gaussian_localized_continuity_compl_le
#print axioms GaussianEllipsoid.Localized.gaussian_localized_unconditional_probability
#print axioms GaussianEllipsoid.Localized.gaussian_localized_bad_probability_tendsto_zero
#print axioms GaussianEllipsoid.Localized.exists_gaussian_localized_bad_probability_tendsto_zero
