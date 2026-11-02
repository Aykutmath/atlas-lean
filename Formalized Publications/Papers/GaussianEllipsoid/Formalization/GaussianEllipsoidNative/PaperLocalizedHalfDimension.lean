import LocalizedCoordinateCompression
import PaperThetaCap

noncomputable section
open MeasureTheory Finset GaussianEllipsoid GaussianEllipsoid.SmallBall
namespace GaussianEllipsoid.Localized

/-- The precise event F from paper Proposition6.1. Coeff n has Euclidean norm;
the explicitly coerced function V has the finite sup norm. -/
def paperLocalizedBad {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (A β B K c d θ : ℝ) : Set Ω :=
  {ω | ∃ q : ℝ, 0 < q ∧ ∃ I : Finset (Fin n), (I.card:ℝ) ≤ K*d ∧
    ∃ U V : Coeff n,
      (∀ i ∉ I, U i = 0) ∧ (∀ i ∈ I, V i = 0) ∧
      (∑ i, |U i|) ≤ A*q*Real.sqrt d ∧
      β*q ≤ ‖V‖ ∧ ‖V‖ ≤ B*q ∧
      Real.sqrt d * ‖(fun i : Fin n => V i)‖ ≤ θ*‖V‖ ∧
      spectralNuclearNorm (T ω (U+V)) < c*q*d}

theorem paperLocalizedBad_subset_homogeneousBad {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (A β B K c d θ : ℝ) (hd : 0 ≤ d) (hθ : θ^2 ≤ 1) :
    paperLocalizedBad T A β B K c d θ ⊆ homogeneousBad T A β B K c d := by
  rintro ω ⟨q,hq,I,hI,U,V,hU,hV,ha,hb,hB,hcap,hbad⟩
  refine ⟨q,hq,I,hI,U,V,hU,hV,ha,hb,hB,?_,hbad⟩
  intro i
  have hi : |V i| ≤ ‖(fun j : Fin n => V j)‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun j : Fin n => V j) i
  have hprod := (mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg d)).trans hcap
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.sqrt d*|V i|) hprod 2
  rw [mul_pow, Real.sq_sqrt hd, sq_abs, mul_pow] at hsq
  exact hsq.trans (by nlinarith [mul_le_mul_of_nonneg_right hθ (sq_nonneg ‖V‖)])

/-- Exact h=floor(d/2) localized small-ball estimate, including the paper's
strict theta cap, arbitrary positive scale q, unrestricted sample-dependent
head on ≤Kd indices, and the original continuity event. -/
theorem paper_localized_uniform_smallball
    {α θ A B β K L : ℝ} (hα : α < 1/4)
    (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (hA : 0 < A) (hB : 0 < B) (hβ : 0 < β) (hK : 0 < K) (hL : 0 < L) :
    ∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧ ∃ d₀ : ℕ,
      ∀ d n : ℕ, d₀ ≤ d → (n:ℝ) ≤ α*(d:ℝ)^2 →
      (bilinearGaussianSampleLaw (d/2) n).real
        (paperLocalizedBad (localizedOperator d (d/2) n) A β B K c d θ ∩
          frobeniusContinuity (localizedOperator d (d/2) n) L d) ≤
        Real.exp (-γ*(d:ℝ)^2) := by
  let α' := max α (1/8:ℝ)
  have hα'0 : 0 < α' := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/8) (le_max_right _ _)
  have hα'4 : α' < 1/4 := max_lt hα (by norm_num)
  obtain ⟨c,γ,hc,_,hγ,d₀,hbound⟩ := exists_gaussian_localized_exp_decay hα'0 hα'4 hA hB hβ hK hL
  refine ⟨c,γ,hc,hγ,max 12 d₀,?_⟩
  intro d n hd hn
  have hd12 : 12 ≤ d := (le_max_left _ _).trans hd
  have hdd0 : d₀ ≤ d := (le_max_right _ _).trans hd
  have hn' : (n:ℝ) ≤ α'*(d:ℝ)^2 := hn.trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have htheta2 : θ^2 ≤ 1 := by linarith [paper_theta_sq_lt_half hθ0 hθ]
  calc
    _ ≤ (bilinearGaussianSampleLaw (d/2) n).real
      (homogeneousBad (localizedOperator d (d/2) n) A β B K c d ∩
        frobeniusContinuity (localizedOperator d (d/2) n) L d) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro p hp
      exact ⟨paperLocalizedBad_subset_homogeneousBad _ A β B K c d θ (Nat.cast_nonneg _) htheta2 hp.1,hp.2⟩
    _ ≤ (bilinearGaussianSampleLaw (2*(d/4)) n).real
      (homogeneousBad (localizedOperator d (2*(d/4)) n) A β B K c d ∩
        frobeniusContinuity (localizedOperator d (2*(d/4)) n) L d) :=
      localized_event_probability_dimension_mono d A β B K c L n (2*(d/4)) (d/2)
        (by omega) (by omega)
    _ ≤ _ := hbound d n hdd0 hn'
end GaussianEllipsoid.Localized
#print axioms GaussianEllipsoid.Localized.paper_localized_uniform_smallball
