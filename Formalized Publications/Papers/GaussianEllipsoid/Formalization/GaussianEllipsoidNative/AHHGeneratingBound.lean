import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Finite generating-sum bound, with the recurrence and all scalar hypotheses explicit.
This module supplies no probabilistic recurrence assumption disguised as a theorem. -/
noncomputable section
open scoped BigOperators
namespace AHH

/-- Truncated ordinary generating sum after a positive change of scale. -/
def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), a k

/-- The positive convolution triangle embeds into the product rectangle.
The second coordinate is shifted by one, so the absent `a₀` term is exact. -/
theorem convolution_sum_le (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j, a i * a (j - i)) ≤
      partialSum a n * (∑ k ∈ Finset.range n, a (k + 1)) := by
  rw [Finset.sum_sigma', partialSum, Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_le_sum_of_injOn
    (fun q : Σ (_ : ℕ), ℕ => (q.2, q.1 - q.2 - 1))
  · intro q hq r hr heq
    have hqi : q.2 < q.1 := Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
    have hri : r.2 < r.1 := Finset.mem_range.mp (Finset.mem_sigma.mp hr).2
    have h₁ := congrArg Prod.fst heq
    have h₂ := congrArg Prod.snd heq
    apply Sigma.ext (by dsimp at h₁ h₂; omega)
    simpa using h₁
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hj, hi⟩ := Finset.mem_sigma.mp hq
    simp only [Finset.mem_range] at hj hi
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_range.mpr <;> omega
  · intro q hq
    have hi : q.2 < q.1 := Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
    dsimp
    have he : q.1 - q.2 - 1 + 1 = q.1 - q.2 := by omega
    rw [he]
  · intro z _ _
    exact mul_nonneg (ha _) (ha _)

/-- The summed scalar recurrence. -/
theorem partialSum_step (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hzero : a 0 = 1)
    {A B t : ℝ} (hAt : 0 ≤ A * t) (n : ℕ)
    (hrec : ∀ j ≤ n, a (j + 1) ≤ B * t * a j +
      A * t * ∑ i ∈ Finset.range j, a i * a (j - i)) :
    partialSum a (n + 1) ≤
      1 + B * t * partialSum a n + A * t * partialSum a n * (partialSum a n - 1) := by
  have htail : (∑ k ∈ Finset.range n, a (k + 1)) = partialSum a n - 1 := by
    unfold partialSum
    rw [Finset.sum_range_succ', hzero]
    ring
  have hstep : partialSum a (n + 1) = 1 + ∑ j ∈ Finset.range (n + 1), a (j + 1) := by
    unfold partialSum
    rw [Finset.sum_range_succ', hzero]
    ring
  rw [hstep]
  calc
    _ ≤ 1 + ∑ j ∈ Finset.range (n + 1),
        (B * t * a j + A * t * ∑ i ∈ Finset.range j, a i * a (j - i)) := by
      gcongr with j hj
      exact hrec j (by simp only [Finset.mem_range] at hj; omega)
    _ = 1 + B * t * partialSum a n + A * t *
        (∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j, a i * a (j - i)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [partialSum, add_assoc]
    _ ≤ 1 + B * t * partialSum a n + A * t *
        (partialSum a n * (partialSum a n - 1)) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        (by simpa only [htail] using convolution_sum_le a ha n) hAt) _
    _ = _ := by ring

/-- The finite generating induction, stated for a supplied positive fixed point. -/
theorem partialSum_le_fixedPoint (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hzero : a 0 = 1) {A B t R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hR : 1 ≤ R) (hfix : 1 + B * t * R + A * t * R * (R - 1) = R)
    (m : ℕ) (hrec : ∀ j < m, a (j + 1) ≤ B * t * a j +
      A * t * ∑ i ∈ Finset.range j, a i * a (j - i)) :
    ∀ n ≤ m, partialSum a n ≤ R := by
  intro n hn
  induction n with
  | zero => simpa [partialSum, hzero] using hR
  | succ n ih =>
      have hnm : n ≤ m := by omega
      have hlow : 1 ≤ partialSum a n := by
        calc
          1 = ∑ i ∈ ({0} : Finset ℕ), a i := by simp [hzero]
          _ ≤ partialSum a n := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · simp [partialSum]
            · intro i _ _; exact ha i
      have hi := ih hnm
      calc
        partialSum a (n + 1) ≤ 1 + B * t * partialSum a n +
            A * t * partialSum a n * (partialSum a n - 1) :=
          partialSum_step a ha hzero (mul_nonneg hA ht) n (fun j hj => hrec j (by omega))
        _ ≤ 1 + B * t * R + A * t * R * (R - 1) := by
          gcongr
        _ = R := hfix

/-- Scaling a finite nonnegative recurrence preserves its precise missing-endpoint convolution. -/
theorem scaled_recurrence (e : ℕ → ℝ) {A B t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hrec : e (n + 1) ≤ B * e n + A * ∑ i ∈ Finset.range n, e i * e (n - i)) :
    e (n + 1) * t ^ (n + 1) ≤ B * t * (e n * t ^ n) +
      A * t * ∑ i ∈ Finset.range n, (e i * t ^ i) * (e (n - i) * t ^ (n - i)) := by
  have hc : (∑ i ∈ Finset.range n, e i * e (n - i)) * t ^ (n + 1) =
      t * ∑ i ∈ Finset.range n, (e i * t ^ i) * (e (n - i) * t ^ (n - i)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hn : n = i + (n - i) := by omega
    have hp : t ^ n = t ^ i * t ^ (n - i) := by rw [← pow_add, ← hn]
    rw [pow_succ, hp]
    ring
  calc
    _ ≤ (B * e n + A * ∑ i ∈ Finset.range n, e i * e (n - i)) * t ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hrec (pow_nonneg ht _)
    _ = _ := by rw [add_mul, mul_assoc A, hc, pow_succ]; ring

/-- The recurrence implies a pointwise geometric moment bound at every finite order. -/
theorem moment_le_of_fixedPoint (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (hzero : e 0 = 1)
    {A B t R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 < t)
    (hR : 1 ≤ R) (hfix : 1 + B * t * R + A * t * R * (R - 1) = R)
    (m : ℕ) (hrec : ∀ j < m, e (j + 1) ≤ B * e j +
      A * ∑ i ∈ Finset.range j, e i * e (j - i)) :
    e m ≤ R / t ^ m := by
  let a : ℕ → ℝ := fun i => e i * t ^ i
  have ha : ∀ i, 0 ≤ a i := fun i => mul_nonneg (he i) (pow_nonneg ht.le i)
  have haz : a 0 = 1 := by simp [a, hzero]
  have har : ∀ j < m, a (j + 1) ≤ B * t * a j +
      A * t * ∑ i ∈ Finset.range j, a i * a (j - i) :=
    fun j hj => scaled_recurrence e ht.le j (hrec j hj)
  have hsum := partialSum_le_fixedPoint a ha haz hA hB ht.le hR hfix m har m le_rfl
  have hm : a m ≤ partialSum a m := by
    apply Finset.single_le_sum (fun i _ => ha i)
    simp
  exact (le_div_iff₀ (pow_pos ht m)).mpr (hm.trans hsum)

/-- Exact upper edge in the finite generating argument. -/
def edgeL (A B : ℝ) : ℝ := (Real.sqrt A + Real.sqrt B) ^ 2

/-- Positive fixed-point value. -/
def edgeR (A B : ℝ) : ℝ := 1 + Real.sqrt (B / A)

theorem edgeL_pos {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) : 0 < edgeL A B := by
  apply sq_pos_of_pos
  exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hA) (Real.sqrt_nonneg B)

theorem edgeR_ge_one (A B : ℝ) : 1 ≤ edgeR A B := by
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

/-- Direct algebraic verification of the fixed point; no Narayana-number bound is used. -/
theorem edge_fixedPoint {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    1 + B * (edgeL A B)⁻¹ * edgeR A B +
      A * (edgeL A B)⁻¹ * edgeR A B * (edgeR A B - 1) = edgeR A B := by
  have hu : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hv : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have huv : Real.sqrt A + Real.sqrt B ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hu hv)
  rw [edgeR, Real.sqrt_div hB, edgeL]
  have hA' := Real.sq_sqrt hA.le
  have hB' := Real.sq_sqrt hB
  field_simp
  nlinarith [sq_nonneg (Real.sqrt A), sq_nonneg (Real.sqrt B)]

/-- The complete finite scalar generating-sum theorem: `e_m ≤ R L^m`. -/
theorem moment_le_edge (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (hzero : e 0 = 1)
    {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (m : ℕ)
    (hrec : ∀ j < m, e (j + 1) ≤ B * e j +
      A * ∑ i ∈ Finset.range j, e i * e (j - i)) :
    e m ≤ edgeR A B * edgeL A B ^ m := by
  have h := moment_le_of_fixedPoint e he hzero hA.le hB
    (inv_pos.mpr (edgeL_pos hA hB)) (edgeR_ge_one A B) (edge_fixedPoint hA hB) m hrec
  simpa [div_eq_mul_inv] using h

end AHH
