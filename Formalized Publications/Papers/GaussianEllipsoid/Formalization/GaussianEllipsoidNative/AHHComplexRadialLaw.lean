import AHHRadialTransport
import AHHGaussianRowLaw

/-! The literal independent-real Gaussian construction has exactly the complex
radial Gaussian distribution. The real dimension is 2h, with all scale factors
proved in the measure identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators
namespace AHHRadial

abbrev CE (h : ℕ) := EuclideanSpace ℂ (Fin h)
abbrev RE (h : ℕ) := EuclideanSpace ℝ (Fin h × Bool)

/-- Explicit real/imaginary identification, including its norm proof. -/
def complexRealIsometry (h : ℕ) : RE h ≃ₗᵢ[ℝ] CE h where
  toLinearEquiv :=
    { toFun := fun x => WithLp.toLp 2 (fun j => (x (j,false) : ℂ) + Complex.I * x (j,true))
      invFun := fun z => WithLp.toLp 2 (fun p => if p.2 then (z p.1).im else (z p.1).re)
      left_inv := by
        intro x
        ext ⟨j,b⟩
        cases b <;> simp
      right_inv := by
        intro z
        ext j
        apply Complex.ext <;> simp
      map_add' := by
        intro x y
        ext j
        simp only [PiLp.add_apply, Complex.ofReal_add]
        ring
      map_smul' := by
        intro c x
        ext j
        simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
          Complex.real_smul, RingHom.id_apply]
        ring }
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
    <;> ring

@[simp] theorem complexRealIsometry_apply (h : ℕ) (x : RE h) (j : Fin h) :
    complexRealIsometry h x j = (x (j,false) : ℂ) + Complex.I * x (j,true) := rfl

open AHHGaussian

/-- The scaled real Gaussian becomes the exact isotropic complex radial law. -/
theorem scaled_complexRealIsometry_gaussian (h : ℕ) (hh : 0 < h) :
    (euclideanGaussianLaw (Fin h × Bool)).map
      (fun x => (Real.sqrt (2*(h : ℝ)))⁻¹ • complexRealIsometry h x) =
        radialGaussianLaw (volume : Measure (CE h)) h := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  have hs : 0 < Real.sqrt (2*(h : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hb : (1/2 : ℝ) / ((Real.sqrt (2*(h : ℝ)))⁻¹)^2 = h := by
    rw [inv_pow, div_inv_eq_mul, Real.sq_sqrt (by positivity)]
    ring
  rw [euclideanGaussianLaw_eq_radialGaussianLaw]
  change Measure.map ((fun z : CE h => (Real.sqrt (2*(h : ℝ)))⁻¹ • z) ∘
    complexRealIsometry h) _ = _
  rw [← Measure.map_map (by fun_prop) (complexRealIsometry h).continuous.measurable,
    map_radialGaussian_isometry _ _ (by norm_num) (complexRealIsometry h)
      (complexRealIsometry h).measurePreserving,
    map_radialGaussian_smul _ (by norm_num) (inv_pos.mpr hs), hb]

/-- The plus-sign literal (a+i a′)/√(2h) has the actual radial law. -/
theorem normalizedRow_true_law (h : ℕ) (hh : 0 < h) :
    (pairRealRowLaw h).map (normalizedRow h true) =
      radialGaussianLaw (volume : Measure (CE h)) h := by
  have hp : (gaussianProductLaw (Fin h × Bool)).map
      (fun x => (fun j => x (j,false), fun j => x (j,true))) = pairRealRowLaw h :=
    gaussian_bool_split_preserving.map_eq
  rw [← hp, Measure.map_map (by unfold normalizedRow normalizedCoordinate; fun_prop) (by fun_prop)]
  have he : (normalizedRow h true ∘
      (fun x : (Fin h × Bool) → ℝ => (fun j => x (j,false), fun j => x (j,true)))) =
      (fun x : RE h => (Real.sqrt (2*(h : ℝ)))⁻¹ • complexRealIsometry h x) ∘
        (MeasurableEquiv.toLp 2 ((Fin h × Bool) → ℝ)) := by
    funext x
    ext j
    change ((x (j,false) : ℂ) + Complex.I * (AHHGaussian.sign true : ℂ) * x (j,true)) /
      (Real.sqrt (2*(h : ℝ)) : ℂ) =
        (Real.sqrt (2*(h : ℝ)))⁻¹ • ((x (j,false) : ℂ) + Complex.I * x (j,true))
    simp only [AHHGaussian.sign, ↓reduceIte, Complex.ofReal_one, mul_one,
      Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    ring
  rw [he, ← Measure.map_map (by fun_prop) (MeasurableEquiv.toLp 2 _).measurable]
  exact scaled_complexRealIsometry_gaussian h hh

def complexConjIsometry (h : ℕ) : CE h ≃ₗᵢ[ℝ] CE h :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin h => Complex.conjLIE)

/-- Both sign choices have the same explicitly normalized radial distribution. -/
theorem normalizedRow_law (h : ℕ) (hh : 0 < h) (s : Bool) :
    (pairRealRowLaw h).map (normalizedRow h s) =
      radialGaussianLaw (volume : Measure (CE h)) h := by
  cases s
  · letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
    have he : normalizedRow h false = complexConjIsometry h ∘ normalizedRow h true := by
      funext x
      ext j
      change normalizedCoordinate h false (x.1 j) (x.2 j) =
        star (normalizedCoordinate h true (x.1 j) (x.2 j))
      simp [normalizedCoordinate, AHHGaussian.sign, Complex.star_def]
    rw [he, ← Measure.map_map (complexConjIsometry h).continuous.measurable
      (by unfold normalizedRow normalizedCoordinate; fun_prop), normalizedRow_true_law h hh]
    exact map_radialGaussian_isometry _ _ (by exact_mod_cast hh)
      (complexConjIsometry h) (complexConjIsometry h).measurePreserving
  · exact normalizedRow_true_law h hh

#print axioms complexRealIsometry
#print axioms normalizedRow_law
end AHHRadial
