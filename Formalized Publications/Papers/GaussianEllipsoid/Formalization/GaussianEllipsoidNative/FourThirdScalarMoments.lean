import FractionalScalarMoments

noncomputable section
open MeasureTheory Real Set GaussianTensorMoments GaussianEllipsoidCandidate BMUniformMoment
open scoped ENNReal BigOperators
namespace BMFourThirdMoment

/-- The finite n≤Ad² window is precisely enough to keep the 4/3-power
moments factorial, with constants independent of d and the moment index. -/
lemma quadratic_moment_scale_le {D A : ℝ} (hD : 0 < D) (hA : 1 ≤ A)
    {k : ℕ} (hk : 0 < k) (hwindow : (k:ℝ) ≤ A*D^4) :
    32*(k:ℝ)+2304*(k:ℝ)^2/D^2 ≤ ((32+2304*A)*(k:ℝ))^((3:ℝ)/2) := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hsqrt : Real.sqrt (k:ℝ) ≤ A*D^2 := by
    have hs := Real.sq_sqrt hk0
    have hAA : A ≤ A^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hAA (pow_nonneg hD.le 4)
    have hsn := Real.sqrt_nonneg (k:ℝ)
    have hAn : 0 ≤ A*D^2 := by positivity
    nlinarith [sq_nonneg (Real.sqrt (k:ℝ) - A*D^2)]
  have hthree : (k:ℝ)^((3:ℝ)/2) = (k:ℝ)*Real.sqrt (k:ℝ) := by
    rw [show (3:ℝ)/2 = 1+(1:ℝ)/2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hratio : (k:ℝ)^2/D^2 ≤ A*(k:ℝ)^((3:ℝ)/2) := by
    rw [div_le_iff₀ (sq_pos_of_pos hD), hthree]
    have hh := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ (k:ℝ)*Real.sqrt (k:ℝ) by positivity)
    have hs := Real.sq_sqrt hk0
    nlinarith [Real.sqrt_nonneg (k:ℝ)]
  have hka : (k:ℝ) ≤ (k:ℝ)^((3:ℝ)/2) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num : (1:ℝ)≤3/2)
  have hkb : (k:ℝ)^((3:ℝ)/2) ≤ (k:ℝ)^((3:ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  have hK : 1 ≤ 32+2304*A := by linarith
  have hKpow : 32+2304*A ≤ (32+2304*A)^((3:ℝ)/2) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hK (by norm_num : (1:ℝ)≤3/2)
  calc
    _ ≤ (32+2304*A)*(k:ℝ)^((3:ℝ)/2) := by
      have hh := mul_le_mul_of_nonneg_left hkb (by positivity : 0 ≤ A)
      calc
        _ = 32*(k:ℝ)+2304*((k:ℝ)^2/D^2) := by ring
        _ ≤ 32*(k:ℝ)^((3:ℝ)/2)+2304*(A*(k:ℝ)^((3:ℝ)/2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hka (by norm_num))
            (mul_le_mul_of_nonneg_left (hratio.trans hh) (by norm_num))
        _ = _ := by ring
    _ ≤ (32+2304*A)^((3:ℝ)/2)*(k:ℝ)^((3:ℝ)/2) :=
      mul_le_mul_of_nonneg_right hKpow (Real.rpow_nonneg hk0 _)
    _ = _ := (Real.mul_rpow (by positivity) hk0).symm

/-- The concrete scalar 4/3-moment bound, valid up to the d² moment window. -/
theorem bernstein_fractional_factorial_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (D A : ℝ) (hD : 0 < D) (hA : 1 ≤ A)
    (htail : ∀ t > 0, μ {x | t < bernsteinGauge D (Z x)} ≤ ENNReal.ofReal (2*exp (-t)))
    (k : ℕ) (hwindow : (k:ℝ) ≤ A*D^4) :
    Integrable (fun x => (|Z x|^((4:ℝ)/3))^k) μ ∧
    (∫ x, (|Z x|^((4:ℝ)/3))^k ∂μ) ≤
      (k.factorial : ℝ)*(2*exp 1*(32+2304*A))^k := by
  by_cases hk : k=0
  · subst k; simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let K : ℝ := 32+2304*A
  have hK : 0 < K := by dsimp [K]; linarith
  have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
  have hM := bernstein_even_moment Z hZ D hD htail k hkpos
  have hscale := quadratic_moment_scale_le hD hA hkpos hwindow
  have hm : (∫ x, |Z x|^(2*k) ∂μ) ≤ (((K*(k:ℝ))^((3:ℝ)/2))^k) := by
    exact hM.2.trans (pow_le_pow_left₀ (by positivity) hscale k)
  have hp := fractional_moment_of_integer_moment (fun x => |Z x|^(2*k))
    (hZ.abs.pow_const _) (fun x => by positivity) hM.1
    (show 0 < ((K*(k:ℝ))^((3:ℝ)/2))^k by positivity)
    (by norm_num : 0 ≤ (2:ℝ)/3) (by norm_num : (2:ℝ)/3 ≤ 1) hm
  have hleft (x : Ω) : (|Z x|^(2*k))^((2:ℝ)/3) = (|Z x|^((4:ℝ)/3))^k := by
    rw [pow_mul, ← Real.rpow_pow_comm (pow_nonneg (abs_nonneg _) 2),
      ← Real.rpow_natCast_mul (abs_nonneg _)]
    norm_num
  have hright : ((((K*(k:ℝ))^((3:ℝ)/2))^k))^((2:ℝ)/3) = (K*(k:ℝ))^k := by
    rw [← Real.rpow_pow_comm (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_mul (by positivity)]
    norm_num
  simp_rw [hleft] at hp
  rw [hright] at hp
  refine ⟨hp.1, hp.2.trans ?_⟩
  have hfacpos : (0:ℝ) < k.factorial := by positivity
  have hfac : (k:ℝ)^k ≤ (k.factorial:ℝ)*(exp 1)^k := by
    have h := (div_le_iff₀ hfacpos).1 (Real.pow_div_factorial_le_exp (k:ℝ) (by positivity) k)
    simpa [mul_comm, Real.exp_one_pow] using h
  have htwo : (2:ℝ) ≤ (2:ℝ)^k := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.one_le_iff_ne_zero.mpr hk)
  calc
    2*(K*(k:ℝ))^k = 2*K^k*(k:ℝ)^k := by rw [mul_pow]; ring
    _ ≤ 2*K^k*((k.factorial:ℝ)*(exp 1)^k) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ ≤ (2:ℝ)^k*K^k*((k.factorial:ℝ)*(exp 1)^k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htwo (by positivity)) (by positivity)
    _ = (k.factorial:ℝ)*(2*exp 1*(32+2304*A))^k := by dsimp [K]; simp only [mul_pow]; ring

/-- Actual independent standard-Gaussian diagonal quadratics, with no MGF,
tail, integrability, or moment premise left to supply. -/
theorem centeredDiagonal_fractional_factorial_moment {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (d A : ℝ) (hd : 0 < d) (hA : 1 ≤ A)
    (hw : ∀ i, |w i| ≤ 1/Real.sqrt d) (hs : (∑ i, (w i)^2) ≤ 1)
    (k : ℕ) (hwindow : (k:ℝ) ≤ A*d^2) :
    Integrable (fun z => (|centeredDiagonal w z|^((4:ℝ)/3))^k) (gaussianProductLaw ι) ∧
    (∫ z, (|centeredDiagonal w z|^((4:ℝ)/3))^k ∂gaussianProductLaw ι) ≤
      (k.factorial : ℝ)*(2*exp 1*(32+2304*A))^k := by
  apply bernstein_fractional_factorial_moment (centeredDiagonal w)
    (by unfold centeredDiagonal; fun_prop) (Real.sqrt d) A (Real.sqrt_pos.mpr hd) hA
  · intro t ht
    exact centeredDiagonal_gauge_tail_ennreal w hd hw hs ht.le
  · simpa only [show (Real.sqrt d)^4 = d^2 by nlinarith [Real.sq_sqrt hd.le]] using hwindow

#print axioms quadratic_moment_scale_le
#print axioms bernstein_fractional_factorial_moment
#print axioms centeredDiagonal_fractional_factorial_moment
end BMFourThirdMoment
