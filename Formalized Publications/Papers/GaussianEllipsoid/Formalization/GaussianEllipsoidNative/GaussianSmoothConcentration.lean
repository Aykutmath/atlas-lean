/- Newly reconstructed analytic support, 2026-10-03. Not recovered original bytes.
   Sharp concentration for bounded C1 functions; the nonsmooth limit is separate. -/
import GaussianCovarianceRotation
import GaussianLaplaceTail
import Mathlib.Probability.Moments.MGFAnalytic

noncomputable section
open MeasureTheory ProbabilityTheory Set
open GaussianTensorMoments BMSmoothQuadraticComposition GaussianCovarianceRotation
open scoped BigOperators BoundedContinuousFunction

namespace GaussianSmoothConcentration
variable {d : ℕ}

def expBounded (f : Raw d →ᵇ ℝ) (c : ℝ) : Raw d →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => Real.exp (c*f x))
    (Real.continuous_exp.comp (continuous_const.mul f.continuous)) (Real.exp (|c| * ‖f‖)) (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans ((abs_mul c (f x)).le.trans
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (abs_nonneg c))))

@[simp] theorem expBounded_apply (f : Raw d →ᵇ ℝ) (c : ℝ) (x : Raw d) :
    expBounded f c x = Real.exp (c*f x) := rfl

def expTest (F : SmoothTest (Fin d)) (c : ℝ) : SmoothTest (Fin d) where
  value := expBounded F.value c
  gradient i := c • (expBounded F.value c * F.gradient i)
  hasFDeriv x := by
    have hh := ((F.hasFDeriv x).const_mul c).exp
    convert! hh using 1
    ext z
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.mul_apply, expBounded_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

lemma gradient_pair_le_one (F : SmoothTest (Fin d))
    (hgrad : ∀ x, ∑ i, (F.gradient i x)^2 ≤ 1) (x y : Raw d) :
    ∑ i, F.gradient i x * F.gradient i y ≤ 1 := by
  have hp : 0 ≤ ∑ i, (F.gradient i x - F.gradient i y)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (∑ i, (F.gradient i x - F.gradient i y)^2) =
      (∑ i, (F.gradient i x)^2) + (∑ i, (F.gradient i y)^2) -
        2*(∑ i, F.gradient i x * F.gradient i y) := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at hp
  nlinarith [hgrad x, hgrad y]

/-- Covariance with the decreasing exponential, with the exact unit constant. -/
theorem negative_exp_covariance_le (F : SmoothTest (Fin d))
    (hgrad : ∀ x, ∑ i, (F.gradient i x)^2 ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    (∫ x, F.value x ∂γ d) * (∫ x, Real.exp (-s*F.value x) ∂γ d) -
      (∫ x, F.value x * Real.exp (-s*F.value x) ∂γ d) ≤
        s * ∫ x, Real.exp (-s*F.value x) ∂γ d := by
  let G := expTest F (-s)
  let L := ∫ x, Real.exp (-s*F.value x) ∂γ d
  let H := fun t => ∫ z, covariancePath F G t z ∂γ₂ d
  let D := fun t => ∫ z, pathVelocity F G t z ∂γ₂ d
  have hd (t : ℝ) : HasDerivAt H (D t) t := hasDerivAt_expected_covariancePath F G t
  have hd_bound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (Real.pi/2)) :
      D t ≤ s * Real.sin t * L := by
    have hsint : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
      (by linarith [ht.2, Real.pi_pos])
    have hi : Integrable (fun z : Raw d × Raw d =>
        (∑ i, F.gradient i (first (-t) z) * F.gradient i z.1) *
          Real.exp (-s*F.value z.1)) (γ₂ d) := by
      let b : (Raw d × Raw d) →ᵇ ℝ :=
        (∑ i, (F.gradient i).compContinuous (firstMap (-t)) *
          (F.gradient i).compContinuous fstMap) * (G.value.compContinuous fstMap)
      convert! BMRowInterpolation.integrable_bounded b using 1
      funext z
      simp [b, G, expTest, fstMap, firstMap]
    have heint : Integrable (fun z : Raw d × Raw d => Real.exp (-s*F.value z.1)) (γ₂ d) := by
      convert! BMRowInterpolation.integrable_bounded (G.value.compContinuous fstMap) using 1
    have hi_bound : (∫ z, (∑ i, F.gradient i (first (-t) z) * F.gradient i z.1) *
        Real.exp (-s*F.value z.1) ∂γ₂ d) ≤ L := by
      have hm := integral_mono hi heint (fun z => by
        have hb := mul_le_mul_of_nonneg_right (gradient_pair_le_one F hgrad (first (-t) z) z.1)
          (Real.exp_pos (-s*F.value z.1)).le
        simpa only [one_mul] using hb)
      have hfsteq : (∫ z : Raw d × Raw d, Real.exp (-s*F.value z.1) ∂γ₂ d) = L := by
        simpa only [L, probReal_univ, one_smul] using!
          (integral_fun_fst (μ := γ d) (ν := γ d) (fun x => Real.exp (-s*F.value x)))
      exact hm.trans_eq hfsteq
    have he : D t = s * Real.sin t *
        ∫ z, (∑ i, F.gradient i (first (-t) z) * F.gradient i z.1) *
          Real.exp (-s*F.value z.1) ∂γ₂ d := by
      change (∫ z, pathVelocity F G t z ∂γ₂ d) = _
      rw [expected_pathVelocity]
      have hp (z : Raw d × Raw d) :
          (∑ i, F.gradient i (first (-t) z) * G.gradient i z.1) =
            -s * ((∑ i, F.gradient i (first (-t) z) * F.gradient i z.1) *
              Real.exp (-s*F.value z.1)) := by
        simp only [G, expTest, BoundedContinuousFunction.smul_apply,
          BoundedContinuousFunction.mul_apply, expBounded_apply, smul_eq_mul,
          Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      simp_rw [hp]
      rw [integral_const_mul]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hi_bound (mul_nonneg hs hsint)
  have ha : AntitoneOn (fun t => H t + s*Real.cos t*L) (Icc 0 (Real.pi/2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · intro t ht
      exact ((hd t).add (((Real.hasDerivAt_cos t).const_mul s).mul_const L)).continuousAt.continuousWithinAt
    · intro t ht
      exact ((hd t).add (((Real.hasDerivAt_cos t).const_mul s).mul_const L)).hasDerivWithinAt
    · intro t ht
      have hh := hd_bound t (interior_subset ht)
      nlinarith
  have hb := ha (show (0 : ℝ) ∈ Icc 0 (Real.pi/2) from ⟨le_rfl, by positivity⟩)
    (show Real.pi/2 ∈ Icc 0 (Real.pi/2) from ⟨by positivity, le_rfl⟩) (by positivity)
  have hzero : H 0 = ∫ x, F.value x * Real.exp (-s*F.value x) ∂γ d := by
    simp only [H, covariancePath, first, Real.cos_zero, Real.sin_zero,
      one_smul, zero_smul, add_zero, G, expTest, expBounded_apply]
    simpa only [probReal_univ, one_smul] using!
      (integral_fun_fst (μ := γ d) (ν := γ d) (fun x => F.value x * Real.exp (-s*F.value x)))
  have hlast : H (Real.pi/2) = (∫ x, F.value x ∂γ d) * L := by
    simp only [H, covariancePath, first, Real.cos_pi_div_two, Real.sin_pi_div_two,
      zero_smul, one_smul, zero_add, G, expTest, expBounded_apply]
    convert! integral_prod_mul (μ := γ d) (ν := γ d) (fun x => F.value x)
      (fun x => Real.exp (-s*F.value x)) using 1
  change H (Real.pi/2) + s*Real.cos (Real.pi/2)*L ≤ H 0 + s*Real.cos 0*L at hb
  rw [hzero, hlast, Real.cos_zero, Real.cos_pi_div_two] at hb
  dsimp [L] at hb
  nlinarith

/-- Sharp centered negative Laplace transform for a bounded C1 unit-gradient test. -/
theorem centered_laplace_le (F : SmoothTest (Fin d))
    (hgrad : ∀ x, ∑ i, (F.gradient i x)^2 ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, Real.exp (t*((∫ y, F.value y ∂γ d)-F.value x)) ∂γ d) ≤
      Real.exp (t^2/2) := by
  let m := ∫ y, F.value y ∂γ d
  let K : Raw d →ᵇ ℝ := BoundedContinuousFunction.const _ m - F.value
  have hset : integrableExpSet K (γ d) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    exact integrable_bounded (expBounded K s)
  have hd (s : ℝ) : HasDerivAt (mgf K (γ d))
      (∫ x, K x * Real.exp (s*K x) ∂γ d) s :=
    hasDerivAt_mgf (by simp [hset])
  have hineq (s : ℝ) (hs : 0 ≤ s) :
      (∫ x, K x * Real.exp (s*K x) ∂γ d) ≤ s * mgf K (γ d) s := by
    have hh := negative_exp_covariance_le F hgrad s hs
    let L := ∫ x, Real.exp (-s*F.value x) ∂γ d
    have he (x : Raw d) : Real.exp (s*K x) = Real.exp (s*m) * Real.exp (-s*F.value x) := by
      rw [← Real.exp_add]
      congr 1
      simp only [K, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply]
      ring
    have heint : Integrable (fun x => Real.exp (-s*F.value x)) (γ d) :=
      integrable_bounded (expBounded F.value (-s))
    have hfeint : Integrable (fun x => F.value x * Real.exp (-s*F.value x)) (γ d) :=
      integrable_bounded (F.value * expBounded F.value (-s))
    have hm : mgf K (γ d) s = Real.exp (s*m)*L := by
      unfold mgf
      simp_rw [he]
      rw [integral_const_mul]
    have hdi : (∫ x, K x * Real.exp (s*K x) ∂γ d) =
        Real.exp (s*m) * (m*L - ∫ x, F.value x * Real.exp (-s*F.value x) ∂γ d) := by
      have hp (x : Raw d) : K x * Real.exp (s*K x) =
          Real.exp (s*m) * (m*Real.exp (-s*F.value x) - F.value x*Real.exp (-s*F.value x)) := by
        rw [he]
        simp only [K, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply]
        ring
      simp_rw [hp]
      rw [integral_const_mul, integral_sub (heint.const_mul m) hfeint, integral_const_mul]
    rw [hdi, hm]
    have hb := mul_le_mul_of_nonneg_left hh (Real.exp_pos (s*m)).le
    dsimp only [m, L] at *
    nlinarith
  have hb := GaussianLaplaceTail.laplace_le_of_derivative_le
    (fun s _ => hd s) hineq (by simp [mgf]) ht
  exact hb

#print axioms expTest
#print axioms negative_exp_covariance_le
#print axioms centered_laplace_le
end GaussianSmoothConcentration
