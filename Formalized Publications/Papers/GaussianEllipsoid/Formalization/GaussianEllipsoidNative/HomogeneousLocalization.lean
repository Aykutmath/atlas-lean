import TwoNetLocalization

noncomputable section
open GaussianEllipsoid
open scoped BigOperators

namespace GaussianEllipsoid.Localized

/-- Original homogeneous existential event. The squared coordinate cap is
identical to sqrt(d)*‖V‖∞≤‖V‖₂ when d≥0. -/
def homogeneousBad {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (A β B K c d : ℝ) : Set Ω :=
  {ω | ∃ q : ℝ, 0 < q ∧ ∃ I : Finset (Fin n), (I.card:ℝ) ≤ K*d ∧
    ∃ U V : Coeff n,
      (∀ i ∉ I, U i = 0) ∧ (∀ i ∈ I, V i = 0) ∧
      (∑ i, |U i|) ≤ A*q*Real.sqrt d ∧
      β*q ≤ ‖V‖ ∧ ‖V‖ ≤ B*q ∧
      (∀ i, d*(V i)^2 ≤ ‖V‖^2) ∧
      spectralNuclearNorm (T ω (U+V)) < c*q*d}

/-- Scale normalization is exact and deterministic. In particular no net of
positive scales q, and no countable approximation of q, is needed. -/
theorem homogeneousBad_subset_uniformBad {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (A β B K c d : ℝ) :
    homogeneousBad T A β B K c d ⊆
      uniformBad T (min n ⌊K*d⌋₊) (A*Real.sqrt d) β B d (c*d) := by
  classical
  rintro ω ⟨q,hq,I,hI,U,V,hU,hV,hhead,hlower,hupper,hcap,hbad⟩
  let u : SupportCoeff I := restrict I (q⁻¹ • U)
  let v : SupportCoeff Iᶜ := restrict Iᶜ (q⁻¹ • V)
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hqi : 0 < q⁻¹ := inv_pos.mpr hq
  have heu : extend I u = q⁻¹ • U := by
    apply extend_restrict
    intro i hi
    simp [PiLp.smul_apply, hU i hi]
  have hev : extend Iᶜ v = q⁻¹ • V := by
    apply extend_restrict
    intro i hi
    have hiI : i ∈ I := by simpa only [Finset.mem_compl, not_not] using hi
    simp [PiLp.smul_apply, hV i hiI]
  have hnormv : ‖v‖ = q⁻¹*‖V‖ := by
    rw [← norm_extend Iᶜ v, hev, norm_smul, Real.norm_eq_abs, abs_of_pos hqi]
  have hcard : I.card ≤ min n ⌊K*d⌋₊ := by
    apply le_min
    · simpa only [Fintype.card_fin] using Finset.card_le_univ I
    · exact Nat.le_floor hI
  refine ⟨I,hcard,u,?_,v,?_,?_⟩
  · change (∑ i, |u i|) ≤ A*Real.sqrt d
    rw [← l1_extend I u, heu]
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hqi,
      ← Finset.mul_sum]
    calc
      q⁻¹*(∑ i, |U i|) ≤ q⁻¹*(A*q*Real.sqrt d) := mul_le_mul_of_nonneg_left hhead hqi.le
      _ = A*Real.sqrt d := by field_simp <;> ring
  · refine ⟨?_,?_,?_⟩
    · rw [hnormv]
      calc
        β = q⁻¹*(β*q) := by field_simp
        _ ≤ q⁻¹*‖V‖ := mul_le_mul_of_nonneg_left hlower hqi.le
    · rw [hnormv]
      calc
        q⁻¹*‖V‖ ≤ q⁻¹*(B*q) := mul_le_mul_of_nonneg_left hupper hqi.le
        _ = B := by field_simp
    · intro i
      have hi : v i = q⁻¹*V i := rfl
      rw [hi, hnormv]
      nlinarith [mul_le_mul_of_nonneg_left (hcap i) (sq_nonneg q⁻¹)]
  · have hid : extend I u + extend Iᶜ v = q⁻¹ • (U+V) := by
      rw [heu,hev,smul_add]
    rw [hid,map_smul,spectralNuclear_smul,abs_of_pos hqi]
    calc
      q⁻¹ * spectralNuclearNorm (T ω (U+V)) < q⁻¹*(c*q*d) :=
        mul_lt_mul_of_pos_left hbad hqi
      _ = c*d := by field_simp <;> ring

/-- Coordinate cap equivalence, retaining the familiar unsquared statement. -/
theorem coordinate_cap_iff {n : ℕ} (V : Coeff n) {d : ℝ} (hd : 0 ≤ d) :
    (∀ i, Real.sqrt d * |V i| ≤ ‖V‖) ↔ (∀ i, d*(V i)^2 ≤ ‖V‖^2) := by
  constructor <;> intro h i
  · have hs := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (norm_nonneg V)).mpr (h i)
    simpa only [mul_pow, Real.sq_sqrt hd, sq_abs] using hs
  · apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (norm_nonneg V)).mp
    simpa only [mul_pow, Real.sq_sqrt hd, sq_abs] using h i

end GaussianEllipsoid.Localized

#print axioms GaussianEllipsoid.Localized.homogeneousBad_subset_uniformBad
