import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace GaussianEllipsoid

/-- Every decreasing nonnegative sequence is bounded pointwise by its total
mass divided by the one-based index. -/
theorem antitone_entry_mul_index_le {q : ℕ} (σ : Fin q → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hanti : Antitone σ) {R : ℝ}
    (hmass : ∑ i, σ i ≤ R) (i : Fin q) :
    ((i.val + 1 : ℕ) : ℝ) * σ i ≤ R := by
  calc
    ((i.val + 1 : ℕ) : ℝ) * σ i = ∑ j ∈ Finset.Iic i, σ i := by
      simp [Fin.card_Iic]
    _ ≤ ∑ j ∈ Finset.Iic i, σ j := by
      exact Finset.sum_le_sum (fun j hj => hanti (Finset.mem_Iic.mp hj))
    _ ≤ ∑ j : Fin q, σ j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => hσ j)
    _ ≤ R := hmass

/-- Squared mass of any tail subset is at most total-mass squared divided by
its first one-based index. This is the deterministic singular-value tail bound. -/
theorem antitone_sum_sq_tail_le {q : ℕ} (σ : Fin q → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hanti : Antitone σ) {R : ℝ}
    (hR : 0 ≤ R) (hmass : ∑ i, σ i ≤ R) (I : Finset (Fin q))
    {K : ℕ} (hK : 0 < K) (hI : ∀ i ∈ I, K ≤ i.val + 1) :
    ∑ i ∈ I, (σ i) ^ 2 ≤ R ^ 2 / K := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hpoint (i : Fin q) (hi : i ∈ I) : σ i ≤ R / K := by
    apply (le_div_iff₀ hKreal).mpr
    calc
      σ i * K = (K : ℝ) * σ i := mul_comm _ _
      _ ≤ ((i.val + 1 : ℕ) : ℝ) * σ i :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hI i hi) (hσ i)
      _ ≤ R := antitone_entry_mul_index_le σ hσ hanti hmass i
  have hsum : ∑ i ∈ I, σ i ≤ R := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hσ i)).trans hmass
  calc
    ∑ i ∈ I, (σ i) ^ 2 ≤ ∑ i ∈ I, (R / K) * σ i := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [mul_le_mul_of_nonneg_right (hpoint i hi) (hσ i)]
    _ = (R / K) * ∑ i ∈ I, σ i := (Finset.mul_sum ..).symm
    _ ≤ (R / K) * R := mul_le_mul_of_nonneg_left hsum (div_nonneg hR hKreal.le)
    _ = R ^ 2 / K := by ring

end GaussianEllipsoid
#print axioms GaussianEllipsoid.antitone_entry_mul_index_le
#print axioms GaussianEllipsoid.antitone_sum_sq_tail_le
