import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
open scoped Topology
namespace UCEscape

/-- All coordinate sets of at most k deleted coordinates. -/
def deletedCoordinateSets (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter (fun A => A.card ≤ k)

@[simp] theorem mem_deletedCoordinateSets (n k : ℕ) (A : Finset (Fin n)) :
    A ∈ deletedCoordinateSets n k ↔ A.card ≤ k := by
  simp [deletedCoordinateSets]

theorem deletedCoordinateSets_nonempty (n k : ℕ) : (deletedCoordinateSets n k).Nonempty := by
  exact ⟨∅, by simp⟩

instance deletedCoordinateSets_type_nonempty (n k : ℕ) :
    Nonempty (deletedCoordinateSets n k) := ⟨⟨∅, by simp⟩⟩

/-- Elementary weighted powerset estimate; it requires no binomial asymptotics. -/
theorem deletedCoordinateSets_card_mul_pow_le (n k : ℕ) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ((deletedCoordinateSets n k).card : ℝ) * t ^ k ≤ (1 + t) ^ n := by
  classical
  calc
    ((deletedCoordinateSets n k).card : ℝ) * t ^ k =
        ∑ A ∈ deletedCoordinateSets n k, t ^ k := by simp
    _ ≤ ∑ A ∈ deletedCoordinateSets n k, t ^ A.card := by
      apply Finset.sum_le_sum
      intro A hA
      exact pow_le_pow_of_le_one ht ht1 ((mem_deletedCoordinateSets n k A).mp hA)
    _ ≤ ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset, t ^ A.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro A _ _
      positivity
    _ = (1 + t) ^ n := by
      simpa using (Finset.prod_one_add (f := fun _ : Fin n => t) Finset.univ).symm

/-- A quantitative small-deletion entropy bound with rate t(1-log t). -/
theorem deletedCoordinateSets_card_le_exp (n k : ℕ) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : (k : ℝ) ≤ t * n) :
    ((deletedCoordinateSets n k).card : ℝ) ≤
      Real.exp ((n : ℝ) * t * (1 - Real.log t)) := by
  have hp := deletedCoordinateSets_card_mul_pow_le n k t ht.le ht1
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have he : (1 + t) ^ n ≤ Real.exp ((n : ℝ) * t) := by
    calc
      (1 + t) ^ n ≤ (Real.exp t) ^ n :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have heq : Real.exp ((n : ℝ) * t * (1 - Real.log t)) * t ^ k =
      Real.exp ((n : ℝ) * t * (1 - Real.log t) + (k : ℝ) * Real.log t) := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log ht]
  apply (mul_le_mul_iff_of_pos_right (pow_pos ht k)).mp
  rw [heq]
  apply (hp.trans he).trans
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonpos_right hk hlog
  nlinarith

/-- The deletion entropy rate tends to zero, as required to choose a fixed small
retained-coordinate loss independent of dimension. -/
theorem deletion_entropy_rate_tendsto_zero :
    Filter.Tendsto (fun t : ℝ => t * (1 - Real.log t)) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => t - t * Real.log t) :=
    continuous_id.sub Real.continuous_mul_log
  convert hc.tendsto 0 using 1
  · funext t; ring
  · simp

theorem exists_small_deletion_entropy (η : ℝ) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t * (1 - Real.log t) ≤ η := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t * (1 - Real.log t) < η :=
    (deletion_entropy_rate_tendsto_zero.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds hη)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hone : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨t, ht, h1, hηt⟩ := (hpos.and (hone.and hsmall)).exists
  exact ⟨t, ht, h1.le, hηt.le⟩

#print axioms deletedCoordinateSets_card_le_exp
#print axioms exists_small_deletion_entropy
end UCEscape
