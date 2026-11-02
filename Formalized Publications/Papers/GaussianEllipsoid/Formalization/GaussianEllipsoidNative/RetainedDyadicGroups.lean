import DyadicPartition
import DyadicRegularity
import MultiscaleScalar
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GaussianEllipsoidCandidate

open Finset

noncomputable def recordOffsetBin {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (tail : List ℕ) (j : ℕ) : Finset ι := by
  classical
  exact if t + j ∈ t :: tail then dyadicBin u amp (t + j) else ∅

noncomputable def recordRetainedSupport {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (tail : List ℕ) (T : ℕ) : Finset ι := by
  classical
  exact (Finset.range T).biUnion (recordOffsetBin u amp t tail)

noncomputable def recordOmittedSupport {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (tail : List ℕ) (T N : ℕ) : Finset ι := by
  classical
  exact (Finset.Ico T N).biUnion (recordOffsetBin u amp t tail)

lemma recordOffsetBin_zero {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (tail : List ℕ) :
    recordOffsetBin u amp t tail 0 = dyadicBin u amp t := by
  classical
  simp [recordOffsetBin]

lemma recordOffsetBin_disjoint {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (t : ℕ) (tail : List ℕ)
    (j k : ℕ) (hne : j ≠ k) :
    Disjoint (recordOffsetBin u amp t tail j) (recordOffsetBin u amp t tail k) := by
  classical
  unfold recordOffsetBin
  split_ifs <;> try simp
  exact dyadicBin_disjoint u amp ha (t+j) (t+k) (by omega)

/-- The exact retained support of a regular actual dyadic record group obeys
all cardinality, mass, energy, and coefficient-cap estimates from the paper. -/
theorem retained_group_estimates {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (t : ℕ) (tail : List ℕ)
    (hbase : (dyadicBin u amp t).Nonempty)
    (hsmall : ∀ s ∈ tail, (dyadicBin u amp s).card < 2 * (dyadicBin u amp t).card)
    (T : ℕ) (hT : 0 < T) :
    let I := recordRetainedSupport u amp t tail T
    let S : ℝ := (dyadicBin u amp t).card
    let amp' := amp * (1 / 2 : ℝ)^(t+1)
    let m := ∑ i ∈ I, |u i|
    let Q := ∑ i ∈ I, (u i)^2
    0 < S ∧ 0 < amp' ∧
    S ≤ (I.card : ℝ) ∧ (I.card : ℝ) ≤ 2 * T * S ∧
    amp' * S ≤ m ∧ m ≤ 8 * amp' * S ∧
    amp'^2 * S ≤ Q ∧ Q ≤ (32 / 3 : ℝ) * amp'^2 * S ∧
    ∀ i ∈ I, |u i| ≤ 2 * amp' := by
  classical
  dsimp only
  let bins := recordOffsetBin u amp t tail
  let S : ℝ := (dyadicBin u amp t).card
  let amp' : ℝ := amp * (1 / 2 : ℝ)^(t+1)
  have hS : 0 < S := by
    dsimp [S]
    exact_mod_cast Finset.card_pos.mpr hbase
  have ha' : 0 < amp' := mul_pos ha (pow_pos (by norm_num) _)
  have hcard : ∀ j, ((bins j).card : ℝ) ≤ 2 * S := by
    intro j
    dsimp [bins, recordOffsetBin]
    split_ifs with hj
    · rcases List.mem_cons.mp hj with heq | hmem
      · rw [heq]
        change S ≤ 2 * S
        linarith
      · apply le_of_lt
        dsimp [S]
        exact_mod_cast hsmall (t+j) hmem
    · simp only [Finset.card_empty, Nat.cast_zero]
      linarith
  have hcap : ∀ j i, i ∈ bins j → |u i| ≤ 2 * amp' * (1 / 2 : ℝ)^j := by
    intro j i hi
    dsimp [bins, recordOffsetBin] at hi
    split_ifs at hi with hj
    · have hu := ((mem_dyadicBin u amp (t+j) i).1 hi).2
      have heq : amp * (1 / 2 : ℝ)^(t+j) = 2 * amp' * (1 / 2 : ℝ)^j := by
        dsimp [amp']
        rw [pow_add, pow_succ]
        ring
      rwa [heq] at hu
    · simpa using hi
  have hzero : bins 0 = dyadicBin u amp t := recordOffsetBin_zero u amp t tail
  have hbasecap : ∀ i ∈ bins 0, amp' ≤ |u i| := by
    intro i hi
    rw [hzero] at hi
    exact le_of_lt ((mem_dyadicBin u amp t i).1 hi).1
  have hup := dyadic_bins_upper bins u amp' S ha'.le hS.le T
    (fun j _ => hcard j) (fun j _ i hi => hcap j i hi)
  have hlo := dyadic_bins_lower bins u amp' ha'.le T hT hbasecap
  rw [hzero] at hlo
  have hd : Set.PairwiseDisjoint (↑(Finset.range T) : Set ℕ) bins := by
    intro j hj k hk hne
    exact recordOffsetBin_disjoint u amp ha.le t tail j k hne
  have hm_eq : (∑ i ∈ recordRetainedSupport u amp t tail T, |u i|) =
      ∑ j ∈ Finset.range T, ∑ i ∈ bins j, |u i| := Finset.sum_biUnion hd
  have hQ_eq : (∑ i ∈ recordRetainedSupport u amp t tail T, (u i)^2) =
      ∑ j ∈ Finset.range T, ∑ i ∈ bins j, (u i)^2 := Finset.sum_biUnion hd
  have hsub : dyadicBin u amp t ⊆ recordRetainedSupport u amp t tail T := by
    intro i hi
    apply Finset.mem_biUnion.mpr
    exact ⟨0, Finset.mem_range.mpr hT, by rw [recordOffsetBin_zero]; exact hi⟩
  have hcardlo : S ≤ ((recordRetainedSupport u amp t tail T).card : ℝ) := by
    dsimp [S]
    exact_mod_cast Finset.card_le_card hsub
  have hcardhi : ((recordRetainedSupport u amp t tail T).card : ℝ) ≤ 2 * T * S := by
    have heq := Finset.card_biUnion hd
    change (((Finset.range T).biUnion bins).card : ℝ) ≤ _
    rw [heq, Nat.cast_sum]
    calc
      ∑ j ∈ Finset.range T, ((bins j).card : ℝ) ≤ ∑ _j ∈ Finset.range T, 2 * S :=
        Finset.sum_le_sum (fun j _ => hcard j)
      _ = 2 * T * S := by simp [nsmul_eq_mul]; ring
  refine ⟨hS, ha', hcardlo, hcardhi, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm_eq]
    exact hlo.1
  · rw [hm_eq]
    exact hup.1
  · rw [hQ_eq]
    exact hlo.2
  · rw [hQ_eq]
    exact hup.2
  · intro i hi
    obtain ⟨j, hj, hi⟩ := Finset.mem_biUnion.mp hi
    have hp : (1 / 2 : ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    apply (hcap j i hi).trans
    change 2 * amp' * (1 / 2 : ℝ)^j ≤ 2 * amp'
    simpa using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * amp')

/-- The discarded offsets have the quantitative geometric mass bound. -/
theorem record_omitted_mass {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (t : ℕ) (tail : List ℕ)
    (hsmall : ∀ s ∈ tail, (dyadicBin u amp s).card < 2 * (dyadicBin u amp t).card)
    (T N : ℕ) :
    let amp' := amp * (1 / 2 : ℝ)^(t+1)
    let S : ℝ := (dyadicBin u amp t).card
    let I := recordOmittedSupport u amp t tail T N
    ∑ i ∈ I, |u i| ≤ 8 * amp' * S * (1 / 2 : ℝ)^T := by
  classical
  dsimp only
  let bins := recordOffsetBin u amp t tail
  let S : ℝ := (dyadicBin u amp t).card
  let amp' : ℝ := amp * (1 / 2 : ℝ)^(t+1)
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have ha' : 0 ≤ amp' := mul_nonneg ha (pow_nonneg (by norm_num) _)
  have hcard : ∀ j, ((bins j).card : ℝ) ≤ 2 * S := by
    intro j
    dsimp [bins, recordOffsetBin]
    split_ifs with hj
    · rcases List.mem_cons.mp hj with heq | hmem
      · rw [heq]
        change S ≤ 2 * S
        linarith
      · apply le_of_lt
        dsimp [S]
        exact_mod_cast hsmall (t+j) hmem
    · simp only [Finset.card_empty, Nat.cast_zero]
      linarith
  have hcap : ∀ j i, i ∈ bins j → |u i| ≤ 2 * amp' * (1 / 2 : ℝ)^j := by
    intro j i hi
    dsimp [bins, recordOffsetBin] at hi
    split_ifs at hi with hj
    · have hu := ((mem_dyadicBin u amp (t+j) i).1 hi).2
      have heq : amp * (1 / 2 : ℝ)^(t+j) = 2 * amp' * (1 / 2 : ℝ)^j := by
        dsimp [amp']
        rw [pow_add, pow_succ]
        ring
      rwa [heq] at hu
    · simp at hi
  have hd : Set.PairwiseDisjoint (↑(Finset.Ico T N) : Set ℕ) bins := by
    intro j hj k hk hne
    exact recordOffsetBin_disjoint u amp ha t tail j k hne
  change (∑ i ∈ (Finset.Ico T N).biUnion bins, |u i|) ≤ _
  rw [Finset.sum_biUnion hd]
  apply dyadic_omitted_mass _ amp' S ha' hS T N
  intro j hj
  calc
    ∑ i ∈ bins j, |u i| ≤ ((bins j).card : ℝ) * (2 * amp' * (1 / 2 : ℝ)^j) :=
      bin_mass_le _ _ _ (hcap j)
    _ ≤ (2 * S) * (2 * amp' * (1 / 2 : ℝ)^j) :=
      mul_le_mul_of_nonneg_right (hcard j) (by positivity)
    _ = 4 * amp' * S * (1 / 2 : ℝ)^j := by ring

#print axioms record_omitted_mass
#print axioms recordOffsetBin_zero
#print axioms recordOffsetBin_disjoint
#print axioms retained_group_estimates

end GaussianEllipsoidCandidate
