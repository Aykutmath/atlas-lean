import GaussianRandomCompensator
import PaperExactPrefixPolar

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperCanonicalPolar

def exactPrefixCross {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (X : Fin N → Euclid q × Euclid r) : ℝ :=
  ∑ i, v i * ⟪exactCompletedPrefix u lo hi X i.val (X i).1,(X i).2⟫_ℝ

def exactPrefixVariance {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (X : Fin N → Euclid q × Euclid r) : ℝ :=
  ∑ i, (v i)^2*‖operatorFrobenius (exactCompletedPrefix u lo hi X i.val)‖^2

theorem exactPrefixCross_eq_rowSum {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (X : Fin N → Euclid q × Euclid r) :
    exactPrefixCross u v lo hi X =
      gaussianRowSum (exactAdaptedPrefix u lo hi) (extendCoefficient v) N X := by
  rw [gaussianRowSum_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [exactAdaptedPrefix_on_history u lo hi hlo]
  simp only [extendCoefficient,Fin.isLt,dif_pos]

theorem exactPrefixVariance_eq_rowVariance {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (X : Fin N → Euclid q × Euclid r) :
    exactPrefixVariance u v lo hi X =
      gaussianRowVariance (exactAdaptedPrefix u lo hi) (extendCoefficient v) N X := by
  rw [gaussianRowVariance_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [exactAdaptedPrefix_on_history u lo hi hlo]
  simp only [extendCoefficient,Fin.isLt,dif_pos]

/-- The paper's literal compensated expectation for the canonical exact
partial-polar witnesses, with their genuine random predictable variance and
finite MGF radius. This uses the actual iid Gaussian sample law. -/
theorem paper_exact_polar_compensator {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (B : ℝ) (hB : 0 < B) (hcoef : ∀ i, |v i| ≤ B)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlamB : lam ≤ 1/(Real.sqrt 2*B)) :
    Integrable (fun X : Fin N → Euclid q × Euclid r =>
      Real.exp (-lam*exactPrefixCross u v lo hi X-lam^2*exactPrefixVariance u v lo hi X))
        (gaussianBilinearSampleLaw (Fin N) q r) ∧
    (∫ X : Fin N → Euclid q × Euclid r,
      Real.exp (-lam*exactPrefixCross u v lo hi X-lam^2*exactPrefixVariance u v lo hi X)
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
  have hh := gaussianRowCompensated_integral_le (exactAdaptedPrefix (r:=r) (q:=q) u lo hi)
    (measurable_exactAdaptedPrefix u lo hi)
    (fun k X => (exactAdaptedPrefix_norm_energy u lo hi hlo hsep k X).1)
    (extendCoefficient v) (-lam) hcap N
  simpa only [← exactPrefixCross_eq_rowSum u v lo hi hlo,
    ← exactPrefixVariance_eq_rowVariance u v lo hi hlo,neg_sq] using hh

/-- Choosing the actual coordinate supremum as the radius parameter. -/
theorem paper_exact_polar_compensator_supnorm {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (hv : v ≠ 0) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlamB : lam ≤ 1/(Real.sqrt 2*‖v‖)) :
    (∫ X : Fin N → Euclid q × Euclid r,
      Real.exp (-lam*exactPrefixCross u v lo hi X-lam^2*exactPrefixVariance u v lo hi X)
        ∂gaussianBilinearSampleLaw (Fin N) q r) ≤ 1 := by
  exact (paper_exact_polar_compensator u v lo hi hlo hsep ‖v‖
    (norm_pos_iff.mpr hv) (fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
    lam hlam hlamB).2

/-- A zero cross vector has no MGF-radius restriction; its compensated
exponential is identically one, including empty coefficient families. -/
theorem paper_exact_polar_compensator_zero {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ) (lam : ℝ) :
    (∫ X : Fin N → Euclid q × Euclid r,
      Real.exp (-lam*exactPrefixCross u 0 lo hi X-lam^2*exactPrefixVariance u 0 lo hi X)
        ∂gaussianBilinearSampleLaw (Fin N) q r) = 1 := by
  simp [exactPrefixCross,exactPrefixVariance]
end GaussianEllipsoid.PaperCanonicalPolar
#print axioms GaussianEllipsoid.PaperCanonicalPolar.paper_exact_polar_compensator
