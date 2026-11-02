import AdaptedPrefixWitness

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoidCandidate

/-- The actual random predictable variance, before any deterministic upper bound. -/
def gaussianRowVariance {r q : ℕ}
    (W : ∀ k : ℕ, (Fin k → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (u : ℕ → ℝ) : ∀ k : ℕ, (Fin k → Euclid q × Euclid r) → ℝ
  | 0, _ => 0
  | k+1, X => gaussianRowVariance W u k (Fin.init X) +
      (u k)^2 * ‖operatorFrobenius (W k (Fin.init X))‖^2

theorem measurable_gaussianRowVariance {r q : ℕ}
    (W : ∀ k : ℕ, (Fin k → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (hW : ∀ k, Measurable (W k)) (u : ℕ → ℝ) (k : ℕ) :
    Measurable (gaussianRowVariance W u k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hinit : Measurable (Fin.init : (Fin (k+1) → Euclid q × Euclid r) →
        (Fin k → Euclid q × Euclid r)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply i.castSucc
    have hR := (((continuous_operatorFrobenius r q).measurable.comp (hW k)).norm.pow_const 2).comp hinit
    exact (ih.comp hinit).add (hR.const_mul ((u k)^2))

theorem gaussian_bilinear_compensated_lintegral_le {r q : ℕ}
    (W : Euclid q →L[ℝ] Euclid r) (t : ℝ) (ht : t^2*‖W‖^2 ≤ 1/2) :
    (∫⁻ X : Euclid q × Euclid r,
      ENNReal.ofReal (Real.exp (t*⟪W X.1,X.2⟫_ℝ-t^2*‖operatorFrobenius W‖^2))
      ∂(euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) ≤ 1 := by
  let C := t^2*‖operatorFrobenius W‖^2
  have heq (X : Euclid q × Euclid r) :
      ENNReal.ofReal (Real.exp (t*⟪W X.1,X.2⟫_ℝ-C)) =
      ENNReal.ofReal (Real.exp (-C))*ENNReal.ofReal (Real.exp (t*⟪W X.1,X.2⟫_ℝ)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
    congr 2
    ring
  change (∫⁻ X : Euclid q × Euclid r,
    ENNReal.ofReal (Real.exp (t*⟪W X.1,X.2⟫_ℝ-C)) ∂_) ≤ 1
  simp_rw [heq]
  rw [lintegral_const_mul _ (by fun_prop)]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-C))*ENNReal.ofReal (Real.exp C) :=
      mul_le_mul_right (gaussian_bilinear_lintegral_le W t ht) _
    _ = 1 := by rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]; simp

/-- Exact random-compensator inequality for an arbitrary measurable predictable
Gaussian row process. The MGF radius is imposed only at the chosen real t. -/
theorem gaussianRowCompensated_lintegral_le {r q : ℕ}
    (W : ∀ k : ℕ, (Fin k → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (hW : ∀ k, Measurable (W k)) (hWnorm : ∀ k X, ‖W k X‖ ≤ 1)
    (u : ℕ → ℝ) (t : ℝ) (hcap : ∀ k, (t*u k)^2 ≤ 1/2) (n : ℕ) :
    (∫⁻ X, ENNReal.ofReal (Real.exp
      (t*gaussianRowSum W u n X-t^2*gaussianRowVariance W u n X))
      ∂gaussianBilinearSampleLaw (Fin n) q r) ≤ 1 := by
  induction n with
  | zero => simp [gaussianRowSum,gaussianRowVariance]
  | succ n ih =>
    let ν := (euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))
    let μ := gaussianBilinearSampleLaw (Fin n) q r
    let F : (Fin n → Euclid q × Euclid r) → ℝ≥0∞ := fun X =>
      ENNReal.ofReal (Real.exp (t*gaussianRowSum W u n X-t^2*gaussianRowVariance W u n X))
    let G : (Fin n → Euclid q × Euclid r) × (Euclid q × Euclid r) → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (Real.exp ((t*u n)*⟪W n p.1 p.2.1,p.2.2⟫_ℝ-
        (t*u n)^2*‖operatorFrobenius (W n p.1)‖^2))
    have hF : Measurable F :=
      (((measurable_gaussianRowSum W hW u n).const_mul t).sub
        ((measurable_gaussianRowVariance W hW u n).const_mul (t^2))).exp.ennreal_ofReal
    have hG : Measurable G := by
      have hbil := measurable_predictable_bilinear_row (W n) (hW n)
      have hR : Measurable (fun p : (Fin n → Euclid q × Euclid r) × (Euclid q × Euclid r) =>
          ‖operatorFrobenius (W n p.1)‖^2) :=
        (((continuous_operatorFrobenius r q).measurable.comp (hW n)).norm.pow_const 2).comp measurable_fst
      exact ((hbil.const_mul (t*u n)).sub (hR.const_mul ((t*u n)^2))).exp.ennreal_ofReal
    have hstep : ∀ X, (∫⁻ Y, G (X,Y) ∂ν) ≤ 1 := by
      intro X
      have hn : ‖W n X‖^2 ≤ 1 := by
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hWnorm n X) 2
      exact gaussian_bilinear_compensated_lintegral_le (W n X) (t*u n)
        ((mul_le_mul_of_nonneg_left hn (sq_nonneg (t*u n))).trans (by simpa using hcap n))
    have hp := pi_prefixLast_measurePreserving ν n
    have hp' := MeasurePreserving.symm (prefixLastEquiv n) hp
    calc
      _ = ∫⁻ p : (Fin n → Euclid q × Euclid r) × (Euclid q × Euclid r),
          ENNReal.ofReal (Real.exp (t*gaussianRowSum W u (n+1) (Fin.snoc p.1 p.2)-
            t^2*gaussianRowVariance W u (n+1) (Fin.snoc p.1 p.2))) ∂μ.prod ν := by
        simpa only [prefixLastEquiv_symm_apply,gaussianBilinearSampleLaw,μ] using
          (hp'.lintegral_comp_emb (prefixLastEquiv n).symm.measurableEmbedding
            (fun X => ENNReal.ofReal (Real.exp (t*gaussianRowSum W u (n+1) X-
              t^2*gaussianRowVariance W u (n+1) X)))).symm
      _ = ∫⁻ p, F p.1*G p ∂μ.prod ν := by
        apply lintegral_congr
        intro p
        dsimp only [F,G]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
        congr 2
        simp only [gaussianRowSum,gaussianRowVariance,Fin.init_snoc,Fin.snoc_last]
        ring
      _ ≤ 1 * ∫⁻ X, F X ∂μ := by
        simpa only [Measure.compProd_const] using
          lintegral_predictable_product_le μ (Kernel.const _ ν) F G hF hG 1
            (Filter.Eventually.of_forall hstep)
      _ ≤ 1 := by simpa only [one_mul] using ih

/-- The compensated exponential is integrable, and its genuine expectation is
at most one; integrability is concluded rather than assumed. -/
theorem gaussianRowCompensated_integral_le {r q : ℕ}
    (W : ∀ k : ℕ, (Fin k → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (hW : ∀ k, Measurable (W k)) (hWnorm : ∀ k X, ‖W k X‖ ≤ 1)
    (u : ℕ → ℝ) (t : ℝ) (hcap : ∀ k, (t*u k)^2 ≤ 1/2) (n : ℕ) :
    Integrable (fun X => Real.exp (t*gaussianRowSum W u n X-t^2*gaussianRowVariance W u n X))
      (gaussianBilinearSampleLaw (Fin n) q r) ∧
    (∫ X, Real.exp (t*gaussianRowSum W u n X-t^2*gaussianRowVariance W u n X)
      ∂gaussianBilinearSampleLaw (Fin n) q r) ≤ 1 := by
  let Y := fun X => t*gaussianRowSum W u n X-t^2*gaussianRowVariance W u n X
  have hm : Measurable Y :=
    ((measurable_gaussianRowSum W hW u n).const_mul t).sub
      ((measurable_gaussianRowVariance W hW u n).const_mul (t^2))
  have hb : (∫⁻ X, ENNReal.ofReal (Real.exp (1*Y X))
      ∂gaussianBilinearSampleLaw (Fin n) q r) ≤ ENNReal.ofReal 1 := by
    simpa only [one_mul,ENNReal.ofReal_one] using gaussianRowCompensated_lintegral_le W hW hWnorm u t hcap n
  constructor
  · simpa only [one_mul] using integrable_exp_of_lintegral_bound
      (gaussianBilinearSampleLaw (Fin n) q r) Y hm 1 1 hb
  · simpa only [mgf,one_mul] using mgf_le_of_lintegral_bound
      (gaussianBilinearSampleLaw (Fin n) q r) Y hm 1 1 zero_le_one hb
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.gaussianRowCompensated_integral_le

namespace GaussianEllipsoidCandidate
theorem gaussianRowVariance_eq_fin_sum {r q : ℕ}
    (W : ∀ k : ℕ, (Fin k → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (u : ℕ → ℝ) (n : ℕ) (X : Fin n → Euclid q × Euclid r) :
    gaussianRowVariance W u n X = ∑ i : Fin n, (u i.val)^2 *
      ‖operatorFrobenius (W i.val (fun j : Fin i.val => X ⟨j.val,j.isLt.trans i.isLt⟩))‖^2 := by
  induction n with
  | zero => simp [gaussianRowVariance]
  | succ n ih =>
    rw [gaussianRowVariance,Fin.sum_univ_castSucc,ih]
    rfl
end GaussianEllipsoidCandidate
namespace GaussianEllipsoid
open GaussianEllipsoidCandidate

/-- The actual random variance compensator of the prefix polar cross process. -/
def prefixWitnessVariance {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (X : Fin N → Euclid q × Euclid r) : ℝ :=
  ∑ i, (v i)^2*‖operatorFrobenius (completedPrefixWitness u lo hi X i.val)‖^2

theorem prefixWitnessVariance_eq_rowVariance {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (X : Fin N → Euclid q × Euclid r) :
    prefixWitnessVariance u v lo hi X =
      gaussianRowVariance (adaptedPrefixWitness u lo hi) (extendCoefficient v) N X := by
  rw [gaussianRowVariance_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [adaptedPrefixWitness_on_history u lo hi hlo]
  simp only [extendCoefficient,Fin.isLt,dif_pos]

/-- Literal negative-lambda random-compensator inequality. B bounds the
normalized deterministic coefficients, and lambda has the exact finite radius
0 <= lambda <= 1/(sqrt(2)*B). No almost-sure increment bound is assumed. -/
theorem prefixWitnessCross_compensator_expectation {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (B : ℝ) (hB : 0 < B) (hcoef : ∀ i, |v i| ≤ B)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlamB : lam ≤ 1/(Real.sqrt 2*B)) :
    Integrable (fun X : Fin N → Euclid q × Euclid r =>
      Real.exp (-lam*prefixWitnessCross u v lo hi X-lam^2*prefixWitnessVariance u v lo hi X))
        (gaussianBilinearSampleLaw (Fin N) q r) ∧
    (∫ X : Fin N → Euclid q × Euclid r,
      Real.exp (-lam*prefixWitnessCross u v lo hi X-lam^2*prefixWitnessVariance u v lo hi X)
        ∂gaussianBilinearSampleLaw (Fin N) q r) ≤ 1 := by
  have hs2 : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hprod : lam*(Real.sqrt 2*B) ≤ 1 := (le_div_iff₀ (mul_pos hs2 hB)).mp hlamB
  have hsq : (lam*(Real.sqrt 2*B))^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (mul_nonneg hlam (mul_pos hs2 hB).le) hprod 2
  have hsqrt : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hcap0 (i : Fin N) : (lam*v i)^2 ≤ 1/2 := by
    have hv := pow_le_pow_left₀ (abs_nonneg (v i)) (hcoef i) 2
    rw [sq_abs] at hv
    have hp := mul_le_mul_of_nonneg_left hv (sq_nonneg lam)
    rw [mul_pow,mul_pow,hsqrt] at hsq
    nlinarith
  have hcap : ∀ k, ((-lam)*extendCoefficient v k)^2 ≤ 1/2 := by
    intro k
    unfold extendCoefficient
    split_ifs with hk
    · simpa only [neg_mul,neg_sq] using hcap0 ⟨k,hk⟩
    · norm_num
  have hh := gaussianRowCompensated_integral_le (adaptedPrefixWitness (r:=r) (q:=q) u lo hi)
    (measurable_adaptedPrefixWitness u lo hi)
    (norm_adaptedPrefixWitness_le_one u lo hi hlo hsep)
    (extendCoefficient v) (-lam) hcap N
  simpa only [← prefixWitnessCross_eq_rowSum u v lo hi hlo,
    ← prefixWitnessVariance_eq_rowVariance u v lo hi hlo,neg_sq] using hh
end GaussianEllipsoid
#print axioms GaussianEllipsoid.prefixWitnessCross_compensator_expectation
