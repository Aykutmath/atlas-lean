import MultiscaleIntegrated
import RetainedDyadicGroups

namespace GaussianEllipsoidCandidate

open Finset

/-- All numerical regularity data for an actual retained dyadic group. -/
def RegularRetainedGroup {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (T : ℕ) (g : List ℕ) : Prop :=
  ∃ t tail, g = t :: tail ∧
    let I := recordRetainedSupport u amp t tail T
    let S : ℝ := (dyadicBin u amp t).card
    let a := amp * (1 / 2 : ℝ)^(t+1)
    let m := ∑ i ∈ I, |u i|
    let Q := ∑ i ∈ I, (u i)^2
    0 < S ∧ 0 < a ∧
    S ≤ (I.card : ℝ) ∧ (I.card : ℝ) ≤ 2 * T * S ∧
    a * S ≤ m ∧ m ≤ 8 * a * S ∧
    a^2 * S ≤ Q ∧ Q ≤ (32 / 3 : ℝ) * a^2 * S ∧
    0 < m ∧ 0 < Q ∧ (3 / 32 : ℝ) * S ≤ m^2 / Q ∧ m^2 / Q ≤ 64 * S ∧
    Q ≤ (32 / 3 : ℝ) * m^2 / S ∧
    (∀ i ∈ I, |u i| ≤ 2 * a ∧ |u i| ≤ 16 * Q / m ∧ |u i| ≤ 2 * m / S) ∧
    ∀ N : ℕ, (∑ i ∈ recordOmittedSupport u amp t tail T N, |u i|) ≤
      8 * (1 / 2 : ℝ)^T * m

/-- All regularity inequalities follow for each actual record group. -/
theorem regularRetainedGroup_of_record {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (t : ℕ) (tail : List ℕ)
    (hbase : (dyadicBin u amp t).Nonempty)
    (hsmall : ∀ s ∈ tail, (dyadicBin u amp s).card < 2 * (dyadicBin u amp t).card)
    (T : ℕ) (hT : 0 < T) : RegularRetainedGroup u amp T (t :: tail) := by
  classical
  have hall := retained_group_estimates u amp ha t tail hbase hsmall T hT
  dsimp only at hall
  rcases hall with ⟨hS, ha', hklo, hkhi, hmlo, hmhi, hQlo, hQhi, hcap⟩
  have heff := dyadic_effective_support
    (amp * (1 / 2 : ℝ)^(t+1)) ((dyadicBin u amp t).card : ℝ)
    (∑ i ∈ recordRetainedSupport u amp t tail T, |u i|)
    (∑ i ∈ recordRetainedSupport u amp t tail T, (u i)^2)
    0 ha' hS hmlo hmhi hQlo hQhi (by positivity)
  rcases heff with ⟨hm, hQ, hRlo, hRhi, _, henergy, _⟩
  refine ⟨t, tail, rfl, hS, ha', hklo, hkhi, hmlo, hmhi, hQlo, hQhi,
    hm, hQ, hRlo, hRhi, henergy, ?_, ?_⟩
  · intro i hi
    have hc := hcap i hi
    have heff' := dyadic_effective_support
      (amp * (1 / 2 : ℝ)^(t+1)) ((dyadicBin u amp t).card : ℝ)
      (∑ j ∈ recordRetainedSupport u amp t tail T, |u j|)
      (∑ j ∈ recordRetainedSupport u amp t tail T, (u j)^2)
      (|u i|) ha' hS hmlo hmhi hQlo hQhi hc
    rcases heff' with ⟨_, _, _, _, hcap1, _, hcap2⟩
    exact ⟨hc, hcap1, hcap2⟩
  · intro N
    have ho := record_omitted_mass u amp ha.le t tail hsmall T N
    dsimp only at ho
    have hh := mul_le_mul_of_nonneg_left hmlo
      (by positivity : 0 ≤ 8 * (1 / 2 : ℝ)^T)
    nlinarith

/-- Unconditional construction of regular retained groups for arbitrary finite
coefficient vectors: bin construction, record selection, geometric growth,
and all retained numerical estimates are proved, not supplied as assumptions. -/
theorem exists_regular_retained_groups {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (hcap : ∀ i, |u i| ≤ amp)
    (T : ℕ) (hT : 0 < T) :
    ∃ N : ℕ, ∃ groups : List (List ℕ), 0 < N ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ Finset.range N, i ∈ dyadicBin u amp t) ∧
      (∀ t, N ≤ t → dyadicBin u amp t = ∅) ∧
      groups.flatten = dyadicRecordLevels u amp N ∧
      (∀ g ∈ groups, RegularRetainedGroup u amp T g) ∧
      groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card) := by
  obtain ⟨N, groups, hN, hcover, hempty, hflat, hreg, hchain⟩ :=
    exists_dyadic_record_decomposition u amp ha hcap
  refine ⟨N, groups, hN, hcover, hempty, hflat, ?_, hchain⟩
  intro g hg
  obtain ⟨t, tail, heq, hbase, hsmall⟩ := hreg g hg
  rw [heq]
  exact regularRetainedGroup_of_record u amp ha t tail hbase hsmall T hT

#print axioms regularRetainedGroup_of_record
#print axioms exists_regular_retained_groups

end GaussianEllipsoidCandidate
