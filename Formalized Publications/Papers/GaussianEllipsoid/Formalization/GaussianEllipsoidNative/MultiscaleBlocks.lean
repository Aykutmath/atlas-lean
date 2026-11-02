import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace GaussianEllipsoidCandidate

noncomputable def badCount {ι Ω : Type*} [Fintype ι]
    (E : ι → Set Ω) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ω ∈ E i).card

/-- The elementary subset union bound used for independent coordinate blocks.
It is uniform in the threshold m and needs no asymptotic binomial estimate. -/
theorem measure_many_independent_bad {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (E : ι → Set Ω)
    (hind : iIndepSet E μ) (p : ℝ≥0∞) (hp : ∀ i, μ (E i) ≤ p) (m : ℕ) :
    μ {ω | m ≤ badCount E ω} ≤
      (Nat.choose (Fintype.card ι) m : ℝ≥0∞) * p ^ m := by
  classical
  let N : Finset (Finset ι) := Finset.univ.powersetCard m
  have hsub : {ω | m ≤ badCount E ω} ⊆
      ⋃ s ∈ N, ⋂ i ∈ s, E i := by
    intro ω hω
    have hc : m ≤ (Finset.univ.filter fun i => ω ∈ E i).card := hω
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hc
    have hsN : s ∈ N := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hcard⟩
    simp only [Set.mem_iUnion, Set.mem_iInter]
    exact ⟨s, hsN, fun i hi => (Finset.mem_filter.mp (hs hi)).2⟩
  have hterm : ∀ s ∈ N, μ (⋂ i ∈ s, E i) ≤ p ^ m := by
    intro s hs
    rw [hind.meas_biInter]
    calc
      ∏ i ∈ s, μ (E i) ≤ ∏ _i ∈ s, p := Finset.prod_le_prod' (fun i _ => hp i)
      _ = p ^ m := by
        rw [Finset.prod_const, (Finset.mem_powersetCard.mp hs).2]
  calc
    μ {ω | m ≤ badCount E ω} ≤ μ (⋃ s ∈ N, ⋂ i ∈ s, E i) := measure_mono hsub
    _ ≤ ∑ s ∈ N, μ (⋂ i ∈ s, E i) := measure_biUnion_finset_le N _
    _ ≤ ∑ _s ∈ N, p ^ m := Finset.sum_le_sum hterm
    _ = (Nat.choose (Fintype.card ι) m : ℝ≥0∞) * p ^ m := by
      simp [N, Finset.sum_const, nsmul_eq_mul]

/-- A coarse 2^J bound convenient for majority-bad block tails. -/
theorem measure_many_independent_bad_two_pow {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (E : ι → Set Ω)
    (hind : iIndepSet E μ) (p : ℝ≥0∞) (hp : ∀ i, μ (E i) ≤ p) (m : ℕ) :
    μ {ω | m ≤ badCount E ω} ≤ (2 : ℝ≥0∞) ^ Fintype.card ι * p ^ m := by
  classical
  have hcard : (Finset.univ.powersetCard m : Finset (Finset ι)).card ≤
      (Finset.univ.powerset : Finset (Finset ι)).card := by
    apply Finset.card_le_card
    intro s hs
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hs).1
  have hchoose : Nat.choose (Fintype.card ι) m ≤ 2 ^ Fintype.card ι := by
    simpa using hcard
  have hcast : (Nat.choose (Fintype.card ι) m : ℝ≥0∞) ≤
      (2 : ℝ≥0∞) ^ Fintype.card ι := by exact_mod_cast hchoose
  exact (measure_many_independent_bad μ E hind p hp m).trans
    (mul_le_mul_left hcast _)

#print axioms measure_many_independent_bad
#print axioms measure_many_independent_bad_two_pow

end GaussianEllipsoidCandidate
