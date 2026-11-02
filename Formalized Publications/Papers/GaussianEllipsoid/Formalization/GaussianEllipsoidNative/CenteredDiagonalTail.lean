import CenteredChiSquareMGF
import MultiscaleMGF

open MeasureTheory ProbabilityTheory GaussianTensorMoments
open scoped ENNReal
namespace GaussianEllipsoidCandidate

noncomputable def centeredDiagonal {ι : Type*} [Fintype ι] (w : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, w i * ((x i)^2-1)

private theorem radius_weights {ι : Type*} [Fintype ι] (w : ι → ℝ)
    {b t : ℝ} (hb : 0 < b) (hw : ∀ i, |w i| ≤ b/4)
    (ht : 0 ≤ t) (htb : t ≤ 1/b) : ∀ i, |(-t)*w i| ≤ 1/4 := by
  intro i
  rw [abs_mul, abs_neg, abs_of_nonneg ht]
  have htb' : t*b ≤ 1 := (le_div_iff₀ hb).1 htb
  have hmul := mul_le_mul_of_nonneg_left (hw i) ht
  nlinarith

/-- Finite-radius MGF for a diagonal Gaussian quadratic with normalized
Frobenius energy and an explicit spectral-radius bound. -/
theorem centeredDiagonal_mgf_le {ι : Type*} [Fintype ι] (w : ι → ℝ)
    {b t : ℝ} (hb : 0 < b) (hw : ∀ i, |w i| ≤ b/4)
    (hs : (∑ i, (w i)^2) ≤ 1) (ht : 0 ≤ t) (htb : t ≤ 1/b) :
    mgf (centeredDiagonal w) (gaussianProductLaw ι) (-t) ≤ Real.exp (t^2*4) := by
  have h := gaussian_weighted_centered_squares_mgf_le (fun i => (-t)*w i)
    (radius_weights w hb hw ht htb)
  have he (x : ι → ℝ) : (-t)*centeredDiagonal w x =
      ∑ i, ((-t)*w i)*((x i)^2-1) := by
    simp only [centeredDiagonal, Finset.mul_sum, mul_assoc]
  unfold mgf
  simp_rw [he]
  apply h.trans
  apply Real.exp_le_exp.mpr
  have heq : (∑ i, ((-t)*w i)^2) = t^2 * ∑ i, (w i)^2 := by
    simp only [mul_pow, neg_sq, Finset.mul_sum]
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg t)]

theorem centeredDiagonal_exp_integrable {ι : Type*} [Fintype ι] (w : ι → ℝ)
    {b t : ℝ} (hb : 0 < b) (hw : ∀ i, |w i| ≤ b/4)
    (ht : 0 ≤ t) (htb : t ≤ 1/b) :
    Integrable (fun x => Real.exp ((-t)*centeredDiagonal w x)) (gaussianProductLaw ι) := by
  have hcap := radius_weights w hb hw ht htb
  have h := gaussian_weighted_centered_squares_integrable (fun i => (-t)*w i)
    (fun i => lt_of_le_of_lt (le_trans (le_abs_self _) (hcap i)) (by norm_num))
  simpa only [centeredDiagonal, Finset.mul_sum, mul_assoc] using h

/-- Actual Gaussian lower tail, with no assumed MGF or independence. -/
theorem centeredDiagonal_lower_tail {ι : Type*} [Fintype ι] (w : ι → ℝ)
    {b x : ℝ} (hb : 0 < b) (hw : ∀ i, |w i| ≤ b/4)
    (hs : (∑ i, (w i)^2) ≤ 1) (hx : 0 ≤ x) :
    (gaussianProductLaw ι).real {z | centeredDiagonal w z ≤ -x} ≤
      Real.exp (-(1/4:ℝ)* min (x^2/4) (x/b)) := by
  exact lower_tail_of_mgf_radius (gaussianProductLaw ι) (centeredDiagonal w) 4 b x
    (by norm_num) hb hx
    (fun t ht htb => centeredDiagonal_exp_integrable w hb hw ht htb)
    (fun t ht htb => centeredDiagonal_mgf_le w hb hw hs ht htb)

/-- Actual two-sided quadratic tail from the proved diagonal Gaussian MGF. -/
theorem centeredDiagonal_abs_tail {ι : Type*} [Fintype ι] (w : ι → ℝ)
    {b x : ℝ} (hb : 0 < b) (hw : ∀ i, |w i| ≤ b/4)
    (hs : (∑ i, (w i)^2) ≤ 1) (hx : 0 ≤ x) :
    (gaussianProductLaw ι).real {z | x ≤ |centeredDiagonal w z|} ≤
      2*Real.exp (-(1/4:ℝ)* min (x^2/4) (x/b)) := by
  have hlow := centeredDiagonal_lower_tail w hb hw hs hx
  have hup := centeredDiagonal_lower_tail (fun i => -w i) hb
    (fun i => by simpa using hw i) (by simpa using hs) hx
  have he (z : ι → ℝ) : centeredDiagonal (fun i => -w i) z = -centeredDiagonal w z := by
    simp [centeredDiagonal, Finset.sum_neg_distrib]
  have hset : {z | x ≤ |centeredDiagonal w z|} ⊆
      {z | centeredDiagonal w z ≤ -x} ∪ {z | centeredDiagonal (fun i => -w i) z ≤ -x} := by
    intro z hz
    change x ≤ |centeredDiagonal w z| at hz
    simp only [Set.mem_setOf_eq, Set.mem_union, he]
    rcases le_total 0 (centeredDiagonal w z) with hp | hn
    · rw [abs_of_nonneg hp] at hz
      right
      linarith
    · rw [abs_of_nonpos hn] at hz
      left
      linarith
  calc
    _ ≤ (gaussianProductLaw ι).real
        ({z | centeredDiagonal w z ≤ -x} ∪ {z | centeredDiagonal (fun i => -w i) z ≤ -x}) :=
      measureReal_mono hset
    _ ≤ (gaussianProductLaw ι).real {z | centeredDiagonal w z ≤ -x} +
        (gaussianProductLaw ι).real {z | centeredDiagonal (fun i => -w i) z ≤ -x} :=
      measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- The exact specialized two-tailed Hanson--Wright bound used for BM
uniform integrability: diagonal coefficient energy≤1 and max coefficient
≤d^(-1/2). The constant16 is explicit. -/
theorem centeredDiagonal_normalized_abs_tail {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {d x : ℝ} (hd : 0 < d)
    (hw : ∀ i, |w i| ≤ 1 / Real.sqrt d)
    (hs : (∑ i, (w i)^2) ≤ 1) (hx : 0 ≤ x) :
    (gaussianProductLaw ι).real {z | x ≤ |centeredDiagonal w z|} ≤
      2 * Real.exp (-min (x^2) (x * Real.sqrt d) / 16) := by
  have hb : 0 < 4 / Real.sqrt d := by positivity
  have hcap : ∀ i, |w i| ≤ (4 / Real.sqrt d)/4 := by
    intro i
    convert hw i using 1 <;> ring
  have h := centeredDiagonal_abs_tail w hb hcap hs hx
  have he : -(1/4:ℝ)*min (x^2/4) (x/(4/Real.sqrt d)) =
      -min (x^2) (x*Real.sqrt d)/16 := by
    rw [div_div_eq_mul_div, min_div_div_right (by norm_num : (0:ℝ) ≤ 4)]
    ring
  rwa [he] at h

#print axioms centeredDiagonal_normalized_abs_tail
#print axioms centeredDiagonal_mgf_le
#print axioms centeredDiagonal_exp_integrable
#print axioms centeredDiagonal_lower_tail
#print axioms centeredDiagonal_abs_tail
end GaussianEllipsoidCandidate
