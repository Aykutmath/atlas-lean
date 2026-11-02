import GaussianLocalizedMap
import DisjointBilinearSmallBall
import LocalizationConstants

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianEllipsoid.SmallBall
open scoped BigOperators

namespace GaussianEllipsoid.Localized

/-- The actual Frobenius coefficient-operator control event. -/
def frobeniusContinuity {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r) (L d : ℝ) : Set Ω :=
  {ω | ∀ x, ‖T ω x‖ ≤ L*Real.sqrt d*‖x‖}

/-- Actual fixed-pair small-ball estimate for the internal support nets. The
head is unrestricted in magnitude; all nondegeneracy comes from the tail. -/
theorem gaussian_localized_fixed_pair (r n s : ℕ) (hr : 0 < r) (hrs : r = 2*s)
    (I : Finset (Fin n)) (u : SupportCoeff I) (v : SupportCoeff Iᶜ)
    {β B c d : ℝ} (hβ : 0 < β) (hc : 0 < c) (hd : 0 < d)
    (h2r : 2*(r:ℝ) ≤ d) (h3r : d ≤ 3*(r:ℝ))
    (hv : v ∈ tailClass Iᶜ β B d) :
    (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (localizedOperator d r n p (extend I u + extend Iᶜ v)) <
        (3*c/2)*d} ≤ (1280*c/β)^(r*r) := by
  have hσ : 0 < ‖v‖ := lt_of_lt_of_le hβ hv.1
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hdisj : ∀ i, extend I u i * extend Iᶜ v i = 0 := by
    intro i
    by_cases hi : i ∈ I <;> simp [hi]
  have hvsum : ∑ i, (extend Iᶜ v i)^2 = ‖v‖^2 := by
    rw [← norm_extend Iᶜ v, PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  have hvcap : ∀ i, (extend Iᶜ v i)^2 ≤ ‖v‖^2*(2*(r:ℝ))⁻¹ := by
    intro i
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < 2*(r:ℝ))).mpr
    by_cases hi : i ∈ Iᶜ
    · simp only [extend_apply, dif_pos hi]
      have hh := hv.2.2 ⟨i,hi⟩
      nlinarith [mul_le_mul_of_nonneg_right h2r (sq_nonneg (v ⟨i,hi⟩))]
    · simp only [extend_apply,dif_neg hi,zero_pow (by decide : 2 ≠ 0),zero_mul]
      positivity
  have h := gaussian_bilinear_disjoint_scaled_nuclear_smallball r n s hr hrs
    (extend I u) (extend Iᶜ v) hdisj hσ hd (by positivity : 0 < (3*c/2)*d)
    hvsum hvcap
  have hsub : {p | spectralNuclearNorm (localizedOperator d r n p
      (extend I u + extend Iᶜ v)) < (3*c/2)*d} ⊆
      {p | spectralNuclearNorm (bilinearScaled d r n ((extend I u : Coeff n) + extend Iᶜ v) p) ≤
        (3*c/2)*d} := by
    intro p hp
    change spectralNuclearNorm (localizedOperator d r n p
      (extend I u + extend Iᶜ v)) ≤ (3*c/2)*d
    exact le_of_lt hp
  apply (measureReal_mono hsub).trans
  apply h.trans
  exact pow_le_pow_left₀ (by positivity)
    (localized_probability_base_le hc hβ hv.1 hd.le hrR h3r) _

/-- Unconditional finite-dimensional localized two-net probability bound for
the actual Gaussian product law. No replacement small-ball or net premise is
present. Arbitrary positive scales are normalized exactly. -/
theorem gaussian_localized_finite_probability (r n s : ℕ)
    (hr : 0 < r) (hrs : r = 2*s)
    {A β B K L c d : ℝ} (hA : 0 ≤ A) (hβ : 0 < β) (hB : 0 ≤ B)
    (hL : 0 < L) (hc : 0 < c) (hd : 0 < d)
    (h2r : 2*(r:ℝ) ≤ d) (h3r : d ≤ 3*(r:ℝ)) :
    (bilinearGaussianSampleLaw r n).real
      (homogeneousBad (localizedOperator d r n) A β B K c d ∩
        frobeniusContinuity (localizedOperator d r n) L d) ≤
      (1280*c/β)^(r*r) * (n+1:ℕ)^(min n ⌊K*d⌋₊) *
        (1+8*A*L*Real.sqrt d/c)^(min n ⌊K*d⌋₊) * (1+8*B*L/c)^n := by
  let m := min n ⌊K*d⌋₊
  let δ := c/(4*L)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hthreshold : c*d+2*(L*d)*δ = (3*c/2)*d := by
    dsimp [δ]
    field_simp
    ring
  have hpair : ∀ I : Finset (Fin n), I.card ≤ m →
      ∀ u ∈ headClass I (A*Real.sqrt d), ∀ v ∈ tailClass Iᶜ β B d,
      (bilinearGaussianSampleLaw r n).real
        {p | spectralNuclearNorm (localizedOperator d r n p (extend I u + extend Iᶜ v)) <
          c*d+2*(L*d)*δ} ≤ (1280*c/β)^(r*r) := by
    intro I _ u _ v hv
    rw [hthreshold]
    exact gaussian_localized_fixed_pair r n s hr hrs I u v hβ hc hd h2r h3r hv
  have hh := uniform_two_net_probability (bilinearGaussianSampleLaw r n)
    (localizedOperator d r n) m (R := A*Real.sqrt d) (D := L*d)
    (δ := δ) (τ := c*d) (p := (1280*c/β)^(r*r))
    (by positivity) hB (by positivity) hδ (by positivity) hpair
  have hsub : homogeneousBad (localizedOperator d r n) A β B K c d ∩
      frobeniusContinuity (localizedOperator d r n) L d ⊆
      uniformBad (localizedOperator d r n) m (A*Real.sqrt d) β B d (c*d) ∩
      nuclearContinuity (localizedOperator d r n) (L*d) := by
    rintro p ⟨hp,hpL⟩
    refine ⟨homogeneousBad_subset_uniformBad _ A β B K c d hp, ?_⟩
    exact frobenius_control_nuclear _ hL.le hd.le (by have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith) hpL
  have hhead : 1+2*(A*Real.sqrt d)/δ = 1+8*A*L*Real.sqrt d/c := by
    dsimp [δ]
    field_simp
    ring
  have htail : 1+2*B/δ = 1+8*B*L/c := by
    dsimp [δ]
    field_simp
    ring
  exact (measureReal_mono hsub).trans (by simpa only [hhead,htail,m] using hh)

/-- Even row dimension specialization valid for every d≥12, preserving 1280. -/
theorem gaussian_localized_even_finite_probability (d n : ℕ) (hd : 12 ≤ d)
    {A β B K L c : ℝ} (hA : 0 ≤ A) (hβ : 0 < β) (hB : 0 ≤ B)
    (hL : 0 < L) (hc : 0 < c) :
    (bilinearGaussianSampleLaw (2*(d/4)) n).real
      (homogeneousBad (localizedOperator d (2*(d/4)) n) A β B K c d ∩
        frobeniusContinuity (localizedOperator d (2*(d/4)) n) L d) ≤
      (1280*c/β)^((2*(d/4))*(2*(d/4))) * (n+1:ℕ)^(min n ⌊K*(d:ℝ)⌋₊) *
        (1+8*A*L*Real.sqrt d/c)^(min n ⌊K*(d:ℝ)⌋₊) * (1+8*B*L/c)^n := by
  obtain ⟨hr,h2r,h3r⟩ := even_rows_bounds d hd
  apply gaussian_localized_finite_probability (2*(d/4)) n (d/4) hr rfl
    hA hβ hB hL hc
  · exact_mod_cast (show 0 < d by omega)
  · exact_mod_cast h2r
  · exact_mod_cast h3r

end GaussianEllipsoid.Localized

#print axioms GaussianEllipsoid.Localized.gaussian_localized_fixed_pair
#print axioms GaussianEllipsoid.Localized.gaussian_localized_finite_probability
#print axioms GaussianEllipsoid.Localized.gaussian_localized_even_finite_probability
