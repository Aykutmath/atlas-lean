import RetainedDyadicGroups
import DyadicRegularity
import MultiscaleScalar
import GaussianEllipsoid.DyadicEstimates
import RealRecordGrouping
import MultiscaleIntegrated
import GlobalDyadicRetention
import CutoffGeometry
import GaussianEllipsoid.NormBridges
import ActualGroupMass
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

/-! Source component: RealRetainedGroups -/

set_option maxHeartbeats 400000
namespace GaussianEllipsoidCandidate
open Finset
/-- The exact retained support of a regular actual dyadic record group obeys
all cardinality, mass, energy, and coefficient-cap estimates from the paper. -/
theorem real_retained_group_estimates {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (t : ℕ) (tail : List ℕ)
    (hbase : (dyadicBin u amp t).Nonempty)
    (hsmall : ∀ s ∈ tail, ((dyadicBin u amp s).card : ℝ) < q * (dyadicBin u amp t).card)
    (T : ℕ) (hT : 0 < T) :
    let I := recordRetainedSupport u amp t tail T
    let S : ℝ := (dyadicBin u amp t).card
    let amp' := amp * (1 / 2 : ℝ)^(t+1)
    let m := ∑ i ∈ I, |u i|
    let Q := ∑ i ∈ I, (u i)^2
    0 < S ∧ 0 < amp' ∧
    S ≤ (I.card : ℝ) ∧ (I.card : ℝ) ≤ q * T * S ∧
    amp' * S ≤ m ∧ m ≤ 4 * q * amp' * S ∧
    amp'^2 * S ≤ Q ∧ Q ≤ (16 * q / 3 : ℝ) * amp'^2 * S ∧
    ∀ i ∈ I, |u i| ≤ 2 * amp' := by
  classical
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  dsimp only
  let bins := recordOffsetBin u amp t tail
  let S : ℝ := (dyadicBin u amp t).card
  let amp' : ℝ := amp * (1 / 2 : ℝ)^(t+1)
  have hS : 0 < S := by
    dsimp [S]
    exact_mod_cast Finset.card_pos.mpr hbase
  have ha' : 0 < amp' := mul_pos ha (pow_pos (by norm_num) _)
  have hcard : ∀ j, ((bins j).card : ℝ) ≤ q * S := by
    intro j
    dsimp [bins, recordOffsetBin]
    split_ifs with hj
    · rcases List.mem_cons.mp hj with heq | hmem
      · rw [heq]
        change S ≤ q * S
        nlinarith
      · apply le_of_lt
        dsimp [S]
        exact hsmall (t+j) hmem
    · simp only [Finset.card_empty, Nat.cast_zero]
      nlinarith
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
  have hup := dyadic_bins_upper bins u amp' (q*S/2) ha'.le (by positivity) T
    (fun j _ => by nlinarith [hcard j]) (fun j _ i hi => hcap j i hi)
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
  have hcardhi : ((recordRetainedSupport u amp t tail T).card : ℝ) ≤ q * T * S := by
    have heq := Finset.card_biUnion hd
    change (((Finset.range T).biUnion bins).card : ℝ) ≤ _
    rw [heq, Nat.cast_sum]
    calc
      ∑ j ∈ Finset.range T, ((bins j).card : ℝ) ≤ ∑ _j ∈ Finset.range T, q * S :=
        Finset.sum_le_sum (fun j _ => hcard j)
      _ = q * T * S := by simp [nsmul_eq_mul]; ring
  refine ⟨hS, ha', hcardlo, hcardhi, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm_eq]
    exact hlo.1
  · rw [hm_eq]
    nlinarith [hup.1]
  · rw [hQ_eq]
    exact hlo.2
  · rw [hQ_eq]
    nlinarith [hup.2]
  · intro i hi
    obtain ⟨j, hj, hi⟩ := Finset.mem_biUnion.mp hi
    have hp : (1 / 2 : ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    apply (hcap j i hi).trans
    change 2 * amp' * (1 / 2 : ℝ)^j ≤ 2 * amp'
    simpa using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * amp')

/-- The discarded offsets have the quantitative geometric mass bound. -/
theorem real_record_omitted_mass {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (t : ℕ) (tail : List ℕ)
    (hsmall : ∀ s ∈ tail, ((dyadicBin u amp s).card : ℝ) < q * (dyadicBin u amp t).card)
    (T N : ℕ) :
    let amp' := amp * (1 / 2 : ℝ)^(t+1)
    let S : ℝ := (dyadicBin u amp t).card
    let I := recordOmittedSupport u amp t tail T N
    ∑ i ∈ I, |u i| ≤ 4 * q * amp' * S * (1 / 2 : ℝ)^T := by
  classical
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  dsimp only
  let bins := recordOffsetBin u amp t tail
  let S : ℝ := (dyadicBin u amp t).card
  let amp' : ℝ := amp * (1 / 2 : ℝ)^(t+1)
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have ha' : 0 ≤ amp' := mul_nonneg ha (pow_nonneg (by norm_num) _)
  have hcard : ∀ j, ((bins j).card : ℝ) ≤ q * S := by
    intro j
    dsimp [bins, recordOffsetBin]
    split_ifs with hj
    · rcases List.mem_cons.mp hj with heq | hmem
      · rw [heq]
        change S ≤ q * S
        nlinarith
      · apply le_of_lt
        dsimp [S]
        exact hsmall (t+j) hmem
    · simp only [Finset.card_empty, Nat.cast_zero]
      nlinarith
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
  have hh := dyadic_omitted_mass (fun j => ∑ i ∈ bins j, |u i|) amp' (q*S/2) ha' (by positivity) T N
  apply (show _ ≤ 8*amp'*(q*S/2)*(1/2:ℝ)^T from ?_).trans (le_of_eq (by dsimp [amp', S]; ring))
  apply hh
  intro j hj
  calc
    ∑ i ∈ bins j, |u i| ≤ ((bins j).card : ℝ) * (2 * amp' * (1 / 2 : ℝ)^j) :=
      bin_mass_le _ _ _ (hcap j)
    _ ≤ (q * S) * (2 * amp' * (1 / 2 : ℝ)^j) :=
      mul_le_mul_of_nonneg_right (hcard j) (by positivity)
    _ = 4 * amp' * (q*S/2) * (1 / 2 : ℝ)^j := by ring


#print axioms real_retained_group_estimates
#print axioms real_record_omitted_mass

end GaussianEllipsoidCandidate

/-! Source component: RealDyadicScalars -/

namespace GaussianEllipsoidCandidate
open Finset

/-- Exact arbitrary-real-q effective rank and cap constants in paper lines 1831–1837. -/
theorem real_dyadic_effective_support (q amp S m Q cap : ℝ)
    (hq : 1 < q) (ha : 0 < amp) (hS : 0 < S)
    (hmlo : amp * S ≤ m) (hmhi : m ≤ 4 * q * amp * S)
    (hQlo : amp ^ 2 * S ≤ Q) (hQhi : Q ≤ (16 * q / 3) * amp ^ 2 * S)
    (hcap : cap ≤ 2 * amp) :
    0 < m ∧ 0 < Q ∧
    (3 / (16 * q)) * S ≤ m ^ 2 / Q ∧
    m ^ 2 / Q ≤ 16 * q^2 * S ∧
    cap ≤ 8 * q * Q / m ∧
    Q ≤ (16 * q / 3) * m ^ 2 / S ∧
    cap ≤ 2 * m / S := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hm : 0 < m := lt_of_lt_of_le (mul_pos ha hS) hmlo
  have hQ : 0 < Q := lt_of_lt_of_le (mul_pos (sq_pos_of_pos ha) hS) hQlo
  have hm2lo : (amp * S) ^ 2 ≤ m ^ 2 := (sq_le_sq₀ (by positivity) hm.le).2 hmlo
  have hm2hi : m ^ 2 ≤ (4 * q * amp * S) ^ 2 := (sq_le_sq₀ hm.le (by positivity)).2 hmhi
  refine ⟨hm, hQ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (GaussianEllipsoid.Dyadic.effective_support_bounds hq0 ha hS hmlo hmhi hQlo hQhi).1
  · exact (GaussianEllipsoid.Dyadic.effective_support_bounds hq0 ha hS hmlo hmhi hQlo hQhi).2
  · apply (le_div_iff₀ hm).2
    have hmul := mul_le_mul_of_nonneg_right hcap hm.le
    have hmass := mul_le_mul_of_nonneg_left hmhi (by positivity : 0 ≤ 2 * amp)
    have henergy := mul_le_mul_of_nonneg_left hQlo (show 0 ≤ 8*q by positivity)
    nlinarith
  · apply (le_div_iff₀ hS).2
    have hs := mul_le_mul_of_nonneg_right hQhi hS.le
    have ht := mul_le_mul_of_nonneg_left hm2lo (show 0 ≤ 16*q/3 by positivity)
    nlinarith
  · apply (le_div_iff₀ hS).2
    have hmul := mul_le_mul_of_nonneg_right hcap hS.le
    nlinarith

/-- Finite-horizon version: only existing record successors are assumed. -/
theorem real_geometric_prefix_mul_le (q : ℝ) (S : ℕ → ℝ)
    (hq : 1 < q) (r : ℕ) (hS : ∀ k ≤ r, 0 ≤ S k)
    (hstep : ∀ k < r, q * S k ≤ S (k+1)) :
    (q-1) * (∑ i ∈ range r, S i) ≤ S r := by
  induction r with
  | zero => simpa using hS 0 le_rfl
  | succ r ih =>
    rw [sum_range_succ]
    have hi := ih (fun k hk => hS k (by omega)) (fun k hk => hstep k (by omega))
    have hs := hstep r (by omega)
    nlinarith

/-- Source cumulative support inequalities, with exact q,T dependence. -/
theorem real_cumulative_support_bounds (q T : ℝ) (S k : ℕ → ℝ)
    (hq : 1 < q) (hT : 0 ≤ T) (r : ℕ)
    (hS : ∀ i ≤ r, 0 ≤ S i)
    (hstep : ∀ i < r, q * S i ≤ S (i+1))
    (hk : ∀ i < r, k i ≤ T*q*S i) :
    (∑ i ∈ range r, S i) ≤ S r / (q-1) ∧
    (∑ i ∈ range r, k i) ≤ T*q/(q-1)*S r := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hprefix : (∑ i ∈ range r, S i) ≤ S r / (q-1) := by
    apply (le_div_iff₀ (by linarith : 0 < q-1)).2
    simpa [mul_comm] using real_geometric_prefix_mul_le q S hq r hS hstep
  refine ⟨hprefix, ?_⟩
  calc
    (∑ i ∈ range r, k i) ≤ ∑ i ∈ range r, T*q*S i :=
      sum_le_sum (fun i hi => hk i (mem_range.mp hi))
    _ = T*q*(∑ i ∈ range r, S i) := (mul_sum _ _ _).symm
    _ ≤ T*q*(S r/(q-1)) := mul_le_mul_of_nonneg_left hprefix (by positivity)
    _ = T*q/(q-1)*S r := by ring

#print axioms real_dyadic_effective_support
#print axioms real_geometric_prefix_mul_le
#print axioms real_cumulative_support_bounds
end GaussianEllipsoidCandidate

/-! Source component: RealDyadicConstruction -/

namespace GaussianEllipsoidCandidate

/-- Actual coefficient bins and greedy support-record selection, assembled.
The resulting groups cover precisely the nonempty dyadic levels, preserve
their order, have the required within-group support bounds, and have q-growing
successive record supports. Dynamic range is unrestricted. -/
theorem exists_real_dyadic_record_decomposition {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (hcap : ∀ i, |u i| ≤ amp) :
    ∃ N : ℕ, ∃ groups : List (List ℕ), 0 < N ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ Finset.range N, i ∈ dyadicBin u amp t) ∧
      (∀ t, N ≤ t → dyadicBin u amp t = ∅) ∧
      groups.flatten = dyadicRecordLevels u amp N ∧
      (∀ g ∈ groups, ∃ t ts, g = t :: ts ∧ (dyadicBin u amp t).Nonempty ∧
        ∀ s ∈ ts, ((dyadicBin u amp s).card : ℝ) < q * (dyadicBin u amp t).card) ∧
      groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q fun t => ((dyadicBin u amp t).card : ℝ)) ∧
      GaussianEllipsoid.PaperRealRecord.RecordGrouping q
        (fun t => ((dyadicBin u amp t).card : ℝ)) (dyadicRecordLevels u amp N) groups := by
  obtain ⟨N, hN, hcover, htail⟩ := finite_dyadic_partition u amp ha hcap
  obtain ⟨groups, hgroups⟩ := GaussianEllipsoid.PaperRealRecord.exists_recordGrouping q
    (fun t => ((dyadicBin u amp t).card : ℝ)) (dyadicRecordLevels u amp N)
  refine ⟨N, groups, hN, hcover, htail, hgroups.flatten_eq, ?_, hgroups.chain, hgroups⟩
  intro g hg
  obtain ⟨t, ts, heq, hsmall⟩ := hgroups.regular g hg
  refine ⟨t, ts, heq, ?_, hsmall⟩
  have hflat : t ∈ groups.flatten := List.mem_flatten.mpr ⟨g, hg, by simp [heq]⟩
  rw [hgroups.flatten_eq] at hflat
  exact ((mem_dyadicRecordLevels u amp N t).1 hflat).2

#print axioms exists_real_dyadic_record_decomposition
end GaussianEllipsoidCandidate

/-! Source component: RealRetainedDecomposition -/

namespace GaussianEllipsoidCandidate

open Finset

/-- All numerical regularity data for an actual retained dyadic group. -/
def RealRegularRetainedGroup {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (T : ℕ) (g : List ℕ) : Prop :=
  ∃ t tail, g = t :: tail ∧
    let I := recordRetainedSupport u amp t tail T
    let S : ℝ := (dyadicBin u amp t).card
    let a := amp * (1 / 2 : ℝ)^(t+1)
    let m := ∑ i ∈ I, |u i|
    let Q := ∑ i ∈ I, (u i)^2
    0 < S ∧ 0 < a ∧
    S ≤ (I.card : ℝ) ∧ (I.card : ℝ) ≤ q * T * S ∧
    a * S ≤ m ∧ m ≤ 4 * q * a * S ∧
    a^2 * S ≤ Q ∧ Q ≤ (16 * q / 3 : ℝ) * a^2 * S ∧
    0 < m ∧ 0 < Q ∧ (3 / (16 * q) : ℝ) * S ≤ m^2 / Q ∧ m^2 / Q ≤ 16 * q^2 * S ∧
    Q ≤ (16 * q / 3 : ℝ) * m^2 / S ∧
    (∀ i ∈ I, |u i| ≤ 2 * a ∧ |u i| ≤ 8 * q * Q / m ∧ |u i| ≤ 2 * m / S) ∧
    ∀ N : ℕ, (∑ i ∈ recordOmittedSupport u amp t tail T N, |u i|) ≤
      4 * q * (1 / 2 : ℝ)^T * m

/-- All regularity inequalities follow for each actual record group. -/
theorem realRegularRetainedGroup_of_record {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (t : ℕ) (tail : List ℕ)
    (hbase : (dyadicBin u amp t).Nonempty)
    (hsmall : ∀ s ∈ tail, ((dyadicBin u amp s).card : ℝ) < q * (dyadicBin u amp t).card)
    (T : ℕ) (hT : 0 < T) : RealRegularRetainedGroup q u amp T (t :: tail) := by
  classical
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hall := real_retained_group_estimates q hq u amp ha t tail hbase hsmall T hT
  dsimp only at hall
  rcases hall with ⟨hS, ha', hklo, hkhi, hmlo, hmhi, hQlo, hQhi, hcap⟩
  have heff := real_dyadic_effective_support q
    (amp * (1 / 2 : ℝ)^(t+1)) ((dyadicBin u amp t).card : ℝ)
    (∑ i ∈ recordRetainedSupport u amp t tail T, |u i|)
    (∑ i ∈ recordRetainedSupport u amp t tail T, (u i)^2)
    0 hq ha' hS hmlo hmhi hQlo hQhi (by positivity)
  rcases heff with ⟨hm, hQ, hRlo, hRhi, _, henergy, _⟩
  refine ⟨t, tail, rfl, hS, ha', hklo, hkhi, hmlo, hmhi, hQlo, hQhi,
    hm, hQ, hRlo, hRhi, henergy, ?_, ?_⟩
  · intro i hi
    have hc := hcap i hi
    have heff' := real_dyadic_effective_support q
      (amp * (1 / 2 : ℝ)^(t+1)) ((dyadicBin u amp t).card : ℝ)
      (∑ j ∈ recordRetainedSupport u amp t tail T, |u j|)
      (∑ j ∈ recordRetainedSupport u amp t tail T, (u j)^2)
      (|u i|) hq ha' hS hmlo hmhi hQlo hQhi hc
    rcases heff' with ⟨_, _, _, _, hcap1, _, hcap2⟩
    exact ⟨hc, hcap1, hcap2⟩
  · intro N
    have ho := real_record_omitted_mass q hq u amp ha.le t tail hsmall T N
    dsimp only at ho
    have hh := mul_le_mul_of_nonneg_left hmlo
      (by positivity : 0 ≤ 4 * q * (1 / 2 : ℝ)^T)
    nlinarith

/-- Unconditional construction of regular retained groups for arbitrary finite
coefficient vectors: bin construction, record selection, geometric growth,
and all retained numerical estimates are proved, not supplied as assumptions. -/
theorem exists_real_regular_retained_groups {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (hcap : ∀ i, |u i| ≤ amp)
    (T : ℕ) (hT : 0 < T) :
    ∃ N : ℕ, ∃ groups : List (List ℕ), 0 < N ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ Finset.range N, i ∈ dyadicBin u amp t) ∧
      (∀ t, N ≤ t → dyadicBin u amp t = ∅) ∧
      groups.flatten = dyadicRecordLevels u amp N ∧
      (∀ g ∈ groups, RealRegularRetainedGroup q u amp T g) ∧
      groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q fun t => ((dyadicBin u amp t).card : ℝ)) := by
  obtain ⟨N, groups, hN, hcover, hempty, hflat, hreg, hchain, hgreedy⟩ :=
    exists_real_dyadic_record_decomposition q hq u amp ha hcap
  refine ⟨N, groups, hN, hcover, hempty, hflat, ?_, hchain⟩
  intro g hg
  obtain ⟨t, tail, heq, hbase, hsmall⟩ := hreg g hg
  rw [heq]
  exact realRegularRetainedGroup_of_record q hq u amp ha t tail hbase hsmall T hT

#print axioms realRegularRetainedGroup_of_record
#print axioms exists_real_regular_retained_groups

end GaussianEllipsoidCandidate

/-! Source component: RealGlobalDyadicRetention -/

namespace GaussianEllipsoidCandidate
open Finset

/-- Complete deterministic retained decomposition: all coefficient partitions,
record groups, retained estimates, and the global omitted-l1 estimate are
constructed and proved for every finite vector, without a dynamic-range
hypothesis or any assumed decomposition. -/
theorem exists_real_global_dyadic_retention {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (hcap : ∀ i, |u i| ≤ amp)
    (T : ℕ) (hT : 0 < T) :
    ∃ N : ℕ, ∃ groups : List (List ℕ), 0 < N ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ Finset.range N, i ∈ dyadicBin u amp t) ∧
      (∀ t, N ≤ t → dyadicBin u amp t = ∅) ∧
      groups.flatten = dyadicRecordLevels u amp N ∧
      (∀ g ∈ groups, RealRegularRetainedGroup q u amp T g) ∧
      groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q fun t => ((dyadicBin u amp t).card : ℝ)) ∧
      (∀ i, retainedGroupVector u amp groups T i = 0 ∨
        retainedGroupVector u amp groups T i = u i) ∧
      coefficientMass (u - retainedGroupVector u amp groups T) ≤
        4 * q * (1 / 2 : ℝ)^T * coefficientMass u ∧
      GaussianEllipsoid.PaperRealRecord.RecordGrouping q
        (fun t => ((dyadicBin u amp t).card : ℝ)) (dyadicRecordLevels u amp N) groups := by
  classical
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  obtain ⟨N, groups, hN, hcover0, hempty, hflat, hreg, hchain, hgreedy⟩ :=
    exists_real_dyadic_record_decomposition q hq u amp ha hcap
  have hnodup : groups.flatten.Nodup := by
    rw [hflat]
    exact List.Nodup.filter _ List.nodup_range
  have hgroups := (List.nodup_flatten.mp hnodup).2
  have hsort : groups.flatten.Pairwise (fun s t : ℕ => s < t) := by
    rw [hflat]
    exact List.Pairwise.filter _ List.pairwise_lt_range
  let J := groups.toFinset
  let R : List ℕ → Finset ι := fun g => recordRetainedSupport u amp (g.headD 0) g.tail T
  let O : List ℕ → Finset ι := fun g => recordOmittedSupport u amp (g.headD 0) g.tail T N
  let Rall := J.biUnion R
  let Oall := J.biUnion O
  have hR : Set.PairwiseDisjoint (↑J : Set (List ℕ)) R := by
    apply dyadic_group_supports_disjoint u amp ha.le groups hgroups R
    intro g hg i hi
    obtain ⟨t, tail, heq, _, _⟩ := hreg g hg
    subst g
    exact retained_mem_level u amp t tail T i hi
  have hO : Set.PairwiseDisjoint (↑J : Set (List ℕ)) O := by
    apply dyadic_group_supports_disjoint u amp ha.le groups hgroups O
    intro g hg i hi
    obtain ⟨t, tail, heq, _, _⟩ := hreg g hg
    subst g
    exact omitted_mem_level u amp t tail T N i hi
  have hpart : ∀ g ∈ J, (∑ i ∈ O g, |u i|) ≤
      4 * q * (1 / 2 : ℝ)^T * ∑ i ∈ R g, |u i| := by
    intro g hg
    obtain ⟨t, tail, heq, hbase, hsmall⟩ := hreg g (List.mem_toFinset.mp hg)
    subst g
    dsimp [R, O]
    have hall := real_retained_group_estimates q hq u amp ha t tail hbase hsmall T hT
    dsimp only at hall
    rcases hall with ⟨_, _, _, _, hmlo, _, _, _, _⟩
    have ho := real_record_omitted_mass q hq u amp ha.le t tail hsmall T N
    dsimp only at ho
    have hh := mul_le_mul_of_nonneg_left hmlo
      (by positivity : 0 ≤ 4 * q * (1 / 2 : ℝ)^T)
    nlinarith
  have hcover : ∀ i, u i ≠ 0 → i ∈ Rall ∨ i ∈ Oall := by
    intro i hi
    obtain ⟨s, hsN, his⟩ := (hcover0 i).1 hi
    have hsN' : s < N := Finset.mem_range.mp hsN
    have hslevels : s ∈ dyadicRecordLevels u amp N :=
      (mem_dyadicRecordLevels u amp N s).2 ⟨hsN', ⟨i, his⟩⟩
    have hsflat : s ∈ groups.flatten := by rwa [hflat]
    obtain ⟨g, hg, hsg⟩ := List.mem_flatten.mp hsflat
    obtain ⟨t, tail, heq, hbase, hsmall⟩ := hreg g hg
    subst g
    have hgSorted : (t :: tail).Pairwise (fun s t : ℕ => s < t) :=
      List.Pairwise.sublist (List.sublist_flatten_of_mem hg) hsort
    have htle : t ≤ s := by
      rcases List.mem_cons.mp hsg with heq | hmem
      · omega
      · have hh := (List.pairwise_cons.mp hgSorted).1 s hmem
        omega
    have hts : t + (s - t) = s := Nat.add_sub_of_le htle
    by_cases hret : s - t < T
    · left
      apply Finset.mem_biUnion.mpr
      refine ⟨t :: tail, List.mem_toFinset.mpr hg, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨s-t, Finset.mem_range.mpr hret, ?_⟩
      simpa [recordOffsetBin, hts, hsg] using his
    · right
      apply Finset.mem_biUnion.mpr
      refine ⟨t :: tail, List.mem_toFinset.mpr hg, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨s-t, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      simpa [recordOffsetBin, hts, hsg] using his
  have herror : coefficientMass (u - retainedGroupVector u amp groups T) ≤
      4 * q * (1 / 2 : ℝ)^T * coefficientMass u := by
    have heq : u - retainedGroupVector u amp groups T =
        (fun i => if i ∈ Rall then 0 else u i) := by
      funext i
      change u i - (if i ∈ Rall then u i else 0) = _
      split_ifs <;> simp
    rw [heq]
    exact (residual_mass_le_cover_mass u Rall Oall hcover).trans
      (omitted_union_mass_le u J R O hR hO (4 * q * (1 / 2 : ℝ)^T) (by positivity) hpart)
  refine ⟨N, groups, hN, hcover0, hempty, hflat, ?_, hchain, ?_, herror, hgreedy⟩
  · intro g hg
    obtain ⟨t, tail, heq, hbase, hsmall⟩ := hreg g hg
    rw [heq]
    exact realRegularRetainedGroup_of_record q hq u amp ha t tail hbase hsmall T hT
  · intro i
    unfold retainedGroupVector
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

#print axioms exists_real_global_dyadic_retention
end GaussianEllipsoidCandidate

/-! Source component: RealDyadicNumerics -/

namespace GaussianEllipsoidCandidate
open Finset

/-- The numerical support and effective-support facts are derived from the
constructor's actual retained vectors. -/
theorem real_actual_group_numerical_bounds {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (r : ℕ) (hr : r < groups.length) :
    0 < dyadicGroupScale u amp groups r ∧
    dyadicGroupScale u amp groups r ≤ dyadicGroupSize u amp groups T r ∧
    dyadicGroupSize u amp groups T r ≤ q*T*dyadicGroupScale u amp groups r ∧
    (3/(16*q):ℝ)*dyadicGroupScale u amp groups r ≤
      dyadicGroupEffectiveSupport u amp groups T r ∧
    dyadicGroupEffectiveSupport u amp groups T r ≤
      16*q^2*dyadicGroupScale u amp groups r := by
  have hg : groups[r]?.getD [] ∈ groups := by
    simp only [List.getElem?_eq_getElem hr, Option.getD_some]
    exact List.getElem_mem hr
  obtain ⟨t, tail, heq, h⟩ := hreg _ hg
  dsimp [dyadicGroupScale, dyadicGroupSize, dyadicGroupSupport,
    dyadicGroupEffectiveSupport]
  rw [heq]
  dsimp only [List.headD_cons, List.tail_cons]
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Successor doubling transfers from the actual greedy record relation to
its canonical numerical sequence. -/
theorem real_actual_group_growth {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q fun t => ((dyadicBin u amp t).card : ℝ)))
    (r : ℕ) (hr : r+1 < groups.length) :
    q*dyadicGroupScale u amp groups r ≤ dyadicGroupScale u amp groups (r+1) := by
  have hg (i : ℕ) (hi : i < groups.length) : groups[i]?.getD [] ∈ groups := by
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  obtain ⟨t, tail, ht, _⟩ := hreg _ (hg r (by omega))
  obtain ⟨s, rest, hs, _⟩ := hreg _ (hg (r+1) hr)
  have hsucc := (List.isChain_iff_getElem.mp hchain) r (by omega)
  have hsucc' : GaussianEllipsoid.PaperRealRecord.RecordSuccessor q (fun t => ((dyadicBin u amp t).card : ℝ))
      (groups[r]?.getD []) (groups[r+1]?.getD []) := by
    simpa only [List.getElem?_eq_getElem (by omega : r < groups.length),
      List.getElem?_eq_getElem hr, Option.getD_some, List.get_eq_getElem] using hsucc
  rw [ht, hs] at hsucc'
  have hnat : q * ((dyadicBin u amp t).card : ℝ) ≤ (dyadicBin u amp s).card := by
    simpa [GaussianEllipsoid.PaperRealRecord.RecordSuccessor] using hsucc'
  dsimp [dyadicGroupScale]
  rw [ht, hs]
  dsimp only [List.headD_cons]
  exact hnat

/-- Cumulative record and retained support sums for the actual finite construction. -/
theorem real_actual_group_prefix_bounds {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card : ℝ)))
    (r : ℕ) (hr : r < groups.length) :
    (∑ i ∈ range r, dyadicGroupScale u amp groups i) ≤
      dyadicGroupScale u amp groups r / (q-1) ∧
    (∑ i ∈ range r, dyadicGroupSize u amp groups T i) ≤
      (T:ℝ)*q/(q-1)*dyadicGroupScale u amp groups r := by
  apply real_cumulative_support_bounds q T _ _ hq (by positivity) r
  · intro i hi
    exact (real_actual_group_numerical_bounds q u amp groups T hreg i (by omega)).1.le
  · intro i hi
    exact real_actual_group_growth q u amp groups T hreg hchain i (by omega)
  · intro i hi
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (real_actual_group_numerical_bounds q u amp groups T hreg i (by omega)).2.2.1

#print axioms real_actual_group_numerical_bounds
#print axioms real_actual_group_growth
#print axioms real_actual_group_prefix_bounds
end GaussianEllipsoidCandidate

/-! Source component: RealDyadicNormBridges -/

namespace GaussianEllipsoidCandidate
open Finset

/-- The paper's restriction vector, with the original exact retained support. -/
def realRecordVector {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (amp : ℝ) (t : ℕ) (tail : List ℕ) (T : ℕ) : ι → ℝ := by
  classical
  exact fun i => if i ∈ recordRetainedSupport u amp t tail T then u i else 0

/-- Exact l1 and squared-l2 identities; this is a representation bridge, not
an assumption about a scalar surrogate. -/
theorem realRecordVector_stats {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (amp : ℝ) (t : ℕ) (tail : List ℕ) (T : ℕ) :
    coefficientMass (realRecordVector u amp t tail T) =
      ∑ i ∈ recordRetainedSupport u amp t tail T, |u i| ∧
    GaussianEllipsoid.euclidNorm (realRecordVector u amp t tail T)^2 =
      ∑ i ∈ recordRetainedSupport u amp t tail T, (u i)^2 := by
  classical
  constructor
  · simp [coefficientMass, realRecordVector, apply_ite abs]
  · rw [GaussianEllipsoid.euclidNorm_sq]
    simp [realRecordVector, ite_pow]

/-- The retained set is exactly the nonzero coordinate support of the
restriction, because every dyadic bin has a strictly positive lower endpoint. -/
theorem realRecordVector_support {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (amp : ℝ) (ha : 0 < amp) (t : ℕ) (tail : List ℕ) (T : ℕ) :
    Function.support (realRecordVector u amp t tail T) =
      (recordRetainedSupport u amp t tail T : Set ι) := by
  classical
  ext i
  simp only [Function.mem_support, realRecordVector, Finset.mem_coe]
  by_cases hi : i ∈ recordRetainedSupport u amp t tail T
  · simp only [if_pos hi, hi, iff_true]
    obtain ⟨s, _, hs⟩ := retained_mem_level u amp t tail T i hi
    have h := ((mem_dyadicBin u amp s i).mp hs).1
    have hp : 0 < amp*(1/2:ℝ)^(s+1) := by positivity
    exact abs_pos.mp (lt_trans hp h)
  · simp [hi]

/-- The exact identity behind the paper's Q/m = ||V||₂/sqrt(R). -/
theorem real_effective_rank_sqrt_identity (m Q : ℝ) (hm : 0 < m) (hQ : 0 < Q) :
    Q / m = Real.sqrt Q / Real.sqrt (m^2/Q) := by
  exact GaussianEllipsoid.Dyadic.energy_mass_ratio hm hQ

/-- Every displayed retained group norm and effective-rank inequality, expressed
on the actual vector with its true support, l1, l2, and sup norm. -/
theorem realRecordVector_paper_bounds {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp)
    (t : ℕ) (tail : List ℕ) (T : ℕ)
    (hreg : RealRegularRetainedGroup q u amp T (t :: tail)) :
    let V := realRecordVector u amp t tail T
    let S : ℝ := (dyadicBin u amp t).card
    let a := amp*(1/2:ℝ)^(t+1)
    let m := coefficientMass V
    let Q := GaussianEllipsoid.euclidNorm V^2
    let R := m^2/Q
    Function.support V = (recordRetainedSupport u amp t tail T : Set ι) ∧
    0 < m ∧ 0 < Q ∧
    S ≤ ((recordRetainedSupport u amp t tail T).card:ℝ) ∧
    ((recordRetainedSupport u amp t tail T).card:ℝ) ≤ T*q*S ∧
    a*S ≤ m ∧ m ≤ 4*q*a*S ∧
    a^2*S ≤ Q ∧ Q ≤ (16*q/3)*a^2*S ∧
    (3/(16*q))*S ≤ R ∧ R ≤ 16*q^2*S ∧
    ‖V‖ ≤ 2*a ∧ 2*a ≤ 8*q*Q/m ∧
    8*q*Q/m = 8*q*GaussianEllipsoid.euclidNorm V/Real.sqrt R := by
  classical
  obtain ⟨s, rest, heq, h⟩ := hreg
  have hst : s = t := (List.cons.inj heq.symm).1
  have hrt : rest = tail := (List.cons.inj heq.symm).2
  subst s
  subst rest
  dsimp only at h ⊢
  rcases h with ⟨hS, ha', hklo, hkhi, hmlo, hmhi, hQlo, hQhi,
    hm, hQ, hRlo, hRhi, henergy, hcap, htail⟩
  have hm_eq := (realRecordVector_stats u amp t tail T).1
  have hQ_eq := (realRecordVector_stats u amp t tail T).2
  rw [hm_eq, hQ_eq]
  refine ⟨realRecordVector_support u amp ha t tail T, hm, hQ, hklo, ?_,
    hmlo, hmhi, hQlo, hQhi, hRlo, hRhi, ?_, ?_, ?_⟩
  · simpa [mul_comm, mul_left_comm, mul_assoc] using hkhi
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    dsimp only [realRecordVector]
    split_ifs with hi
    · simpa only [Real.norm_eq_abs] using (hcap i hi).1
    · simp; positivity
  · exact (real_dyadic_effective_support q _ _ _ _ _ hq ha' hS hmlo hmhi hQlo hQhi le_rfl).2.2.2.2.1
  · have heq := real_effective_rank_sqrt_identity _ _ hm hQ
    have hn : GaussianEllipsoid.euclidNorm (realRecordVector u amp t tail T) =
        Real.sqrt (∑ i ∈ recordRetainedSupport u amp t tail T, (u i)^2) := by
      rw [← hQ_eq, Real.sqrt_sq (GaussianEllipsoid.euclidNorm_nonneg _)]
    rw [hn]
    calc
      8*q*(∑ i ∈ recordRetainedSupport u amp t tail T, (u i)^2) /
          (∑ i ∈ recordRetainedSupport u amp t tail T, |u i|) =
        8*q*((∑ i ∈ recordRetainedSupport u amp t tail T, (u i)^2) /
          (∑ i ∈ recordRetainedSupport u amp t tail T, |u i|)) := by ring
      _ = _ := by rw [heq]; ring

/-- Canonical source amplitude is the sup norm, not a freely chosen envelope. -/
theorem exists_real_dyadic_retention_sup_norm {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (hu : u ≠ 0)
    (T : ℕ) (hT : 0 < T) :
    ∃ N : ℕ, ∃ groups : List (List ℕ), 0 < N ∧
      groups.flatten = dyadicRecordLevels u ‖u‖ N ∧
      GaussianEllipsoid.PaperRealRecord.RecordGrouping q
        (fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) (dyadicRecordLevels u ‖u‖ N) groups ∧
      (∀ g ∈ groups, RealRegularRetainedGroup q u ‖u‖ T g) ∧
      groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
        fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) ∧
      coefficientMass (u-retainedGroupVector u ‖u‖ groups T) ≤
        4*q*(1/2:ℝ)^T*coefficientMass u ∧
      (∀ r, r < groups.length →
        (∑ i ∈ range r, dyadicGroupScale u ‖u‖ groups i) ≤
          dyadicGroupScale u ‖u‖ groups r/(q-1) ∧
        (∑ i ∈ range r, dyadicGroupSize u ‖u‖ groups T i) ≤
          (T:ℝ)*q/(q-1)*dyadicGroupScale u ‖u‖ groups r) := by
  have ha : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hcap : ∀ i, |u i| ≤ ‖u‖ := by
    intro i
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
  obtain ⟨N, groups, hN, hcover, hempty, hflat, hreg, hchain, hcoord, herror, hgreedy⟩ :=
    exists_real_global_dyadic_retention q hq u ‖u‖ ha hcap T hT
  exact ⟨N, groups, hN, hflat, hgreedy, hreg, hchain, herror,
    fun r hr => real_actual_group_prefix_bounds q hq u ‖u‖ groups T hreg hchain r hr⟩

#print axioms realRecordVector_stats
#print axioms realRecordVector_support
#print axioms real_effective_rank_sqrt_identity
#print axioms realRecordVector_paper_bounds
#print axioms exists_real_dyadic_retention_sup_norm
end GaussianEllipsoidCandidate

/-! Source component: RealDyadicRepresentations -/

namespace GaussianEllipsoidCandidate
open Finset

/-- The two existing bin representations coincide exactly, including boundary conventions. -/
theorem real_dyadicBin_eq_paper_bin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) :
    dyadicBin u amp t = GaussianEllipsoid.Dyadic.bin u amp t := by
  ext i
  simp only [mem_dyadicBin, GaussianEllipsoid.Dyadic.mem_bin, div_pow, one_pow,
    div_eq_mul_inv, one_div, one_mul, inv_pow]

/-- The list representation applies the level selector before taking a union
of coordinates, exactly as in the repaired source group definition. -/
theorem real_retainedSupport_eq_paper_coords {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (tail : List ℕ) (T : ℕ)
    (hstart : ∀ s ∈ t :: tail, t ≤ s) :
    recordRetainedSupport u amp t tail T =
      GaussianEllipsoid.Dyadic.retainedCoords (GaussianEllipsoid.Dyadic.bin u amp)
        {s | s ∈ t :: tail} t T := by
  ext i
  simp only [recordRetainedSupport, mem_biUnion, mem_range,
    GaussianEllipsoid.Dyadic.retainedCoords, GaussianEllipsoid.Dyadic.mem_levelCoords,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hi⟩
    dsimp [recordOffsetBin] at hi
    split_ifs at hi with hm
    · exact ⟨t+j, ⟨hm, by omega⟩, by rwa [← real_dyadicBin_eq_paper_bin]⟩
    · simp at hi
  · rintro ⟨s, ⟨hs, hcut⟩, hi⟩
    have hts := hstart s hs
    have heq : t+(s-t)=s := by omega
    refine ⟨s-t, by omega, ?_⟩
    simpa [recordOffsetBin, heq, hs, real_dyadicBin_eq_paper_bin] using hi

/-- The finite cutoff used for omitted support removes no level of the actual
group: every input level is less than N, while the paper permits an infinite last group. -/
theorem real_omittedSupport_eq_paper_coords {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (tail : List ℕ) (T N : ℕ)
    (hstart : ∀ s ∈ t :: tail, t ≤ s)
    (hend : ∀ s ∈ t :: tail, s < N) :
    recordOmittedSupport u amp t tail T N =
      GaussianEllipsoid.Dyadic.omittedCoords (GaussianEllipsoid.Dyadic.bin u amp)
        {s | s ∈ t :: tail} t T := by
  ext i
  simp only [recordOmittedSupport, mem_biUnion, mem_Ico,
    GaussianEllipsoid.Dyadic.omittedCoords, GaussianEllipsoid.Dyadic.mem_levelCoords,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, ⟨hjT, hjN⟩, hi⟩
    dsimp [recordOffsetBin] at hi
    split_ifs at hi with hj
    · exact ⟨t+j, ⟨hj, by omega⟩, by rwa [← real_dyadicBin_eq_paper_bin]⟩
    · simp at hi
  · rintro ⟨s, ⟨hs, hTs⟩, hi⟩
    have hts := hstart s hs
    have hsN := hend s hs
    refine ⟨s-t, ⟨by omega, by omega⟩, ?_⟩
    have heq : t+(s-t)=s := by omega
    simpa [recordOffsetBin, heq, hs, real_dyadicBin_eq_paper_bin] using hi

/-- Exact restriction vector bridge to the original paper-facing Dyadic namespace. -/
theorem realRecordVector_eq_paper_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (tail : List ℕ) (T : ℕ)
    (hstart : ∀ s ∈ t :: tail, t ≤ s) :
    realRecordVector u amp t tail T =
      GaussianEllipsoid.Dyadic.restrict u
        (GaussianEllipsoid.Dyadic.retainedCoords (GaussianEllipsoid.Dyadic.bin u amp)
          {s | s ∈ t :: tail} t T) := by
  unfold realRecordVector GaussianEllipsoid.Dyadic.restrict
  rw [real_retainedSupport_eq_paper_coords u amp t tail T hstart]
  funext i
  by_cases hi : i ∈ GaussianEllipsoid.Dyadic.retainedCoords (GaussianEllipsoid.Dyadic.bin u amp)
      {s | s ∈ t :: tail} t T <;> simp [hi]

/-- A group of the actual construction has the sortedness hypotheses required
by the support representation bridge. -/
theorem real_actual_group_level_bounds {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (N t : ℕ) (tail : List ℕ)
    (hflat : groups.flatten = dyadicRecordLevels u amp N)
    (hg : t :: tail ∈ groups) :
    (∀ s ∈ t :: tail, t ≤ s) ∧ (∀ s ∈ t :: tail, s < N) := by
  have hsort : groups.flatten.Pairwise (fun s t : ℕ => s < t) := by
    rw [hflat]
    exact List.Pairwise.filter _ List.pairwise_lt_range
  have hgroup : (t :: tail).Pairwise (fun s t : ℕ => s < t) :=
    List.Pairwise.sublist (List.sublist_flatten_of_mem hg) hsort
  constructor
  · intro s hs
    rcases List.mem_cons.mp hs with hs | hs
    · omega
    · exact ((List.pairwise_cons.mp hgroup).1 s hs).le
  · intro s hs
    have hh : s ∈ groups.flatten := List.mem_flatten.mpr ⟨t :: tail, hg, hs⟩
    rw [hflat] at hh
    exact ((mem_dyadicRecordLevels u amp N s).mp hh).1

/-- Actual retained supports of distinct groups are disjoint at arbitrary q. -/
theorem real_actual_retained_disjoint {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T N : ℕ)
    (hflat : groups.flatten = dyadicRecordLevels u amp N)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g) :
    Set.PairwiseDisjoint (↑groups.toFinset : Set (List ℕ))
      (fun g => recordRetainedSupport u amp (g.headD 0) g.tail T) := by
  classical
  apply dyadic_group_supports_disjoint u amp ha groups
  · apply (List.nodup_flatten.mp ?_).2
    rw [hflat]
    exact List.Nodup.filter _ List.nodup_range
  · intro g hg i hi
    obtain ⟨t, tail, heq, _⟩ := hreg g hg
    subst g
    exact retained_mem_level u amp t tail T i hi

/-- Disjoint finite coordinate restrictions add to the restriction on their union. -/
theorem real_restrict_union_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (J : Finset κ) (R : κ → Finset ι)
    (hR : Set.PairwiseDisjoint (↑J : Set κ) R) :
    (fun i => if i ∈ J.biUnion R then u i else 0) =
      ∑ g ∈ J, (fun i => if i ∈ R g then u i else 0) := by
  classical
  funext i
  simp only [Finset.sum_apply]
  have hh := Finset.sum_biUnion hR (f := fun k => if k=i then u i else 0)
  simpa using hh

/-- The constructed global retained vector is literally the sum of V_r. -/
theorem real_retainedGroupVector_eq_sum {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T N : ℕ)
    (hflat : groups.flatten = dyadicRecordLevels u amp N)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g) :
    retainedGroupVector u amp groups T =
      ∑ g ∈ groups.toFinset, realRecordVector u amp (g.headD 0) g.tail T := by
  classical
  exact real_restrict_union_sum u groups.toFinset _
    (real_actual_retained_disjoint q u amp ha groups T N hflat hreg)

/-- The source's zero-vector convention is realized exactly. -/
theorem real_zero_dyadic_retention {ι : Type*} [Fintype ι] (T : ℕ) :
    retainedGroupVector (0 : ι → ℝ) 0 [] T = 0 ∧
    (0 : ι → ℝ) - retainedGroupVector 0 0 [] T = 0 := by
  constructor <;> ext i <;> simp [retainedGroupVector, retainedGroupUnion]

#print axioms real_dyadicBin_eq_paper_bin
#print axioms real_retainedSupport_eq_paper_coords
#print axioms real_omittedSupport_eq_paper_coords
#print axioms realRecordVector_eq_paper_restrict
#print axioms real_actual_group_level_bounds
#print axioms real_actual_retained_disjoint
#print axioms real_restrict_union_sum
#print axioms real_retainedGroupVector_eq_sum
#print axioms real_zero_dyadic_retention
end GaussianEllipsoidCandidate

/-! Source component: RealDyadicSharpBudgets -/

namespace GaussianEllipsoidCandidate
open Finset

/-- Literal infinite geometric factors in the three displayed budgets. -/
theorem real_dyadic_series_values (T : ℕ) :
    (∑' j : ℕ, (1/2:ℝ)^(j+1)) = 1 ∧
    (∑' j : ℕ, (1/4:ℝ)^(j+1)) = 1/3 ∧
    (∑' j : ℕ, (1/2:ℝ)^(T+j)) = 2*(1/2:ℝ)^T := by
  have hhalf : (∑' j : ℕ, (1/2:ℝ)^j) = 2 := tsum_geometric_two
  have hquarter : (∑' j : ℕ, (1/4:ℝ)^j) = 4/3 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [pow_succ]
    rw [tsum_mul_right, hhalf]
    norm_num
  · simp_rw [pow_succ]
    rw [tsum_mul_right, hquarter]
    norm_num
  · simp_rw [pow_add]
    rw [tsum_mul_left, hhalf]
    ring

/-- The sharp first-step mass and energy budgets retain the base level's own
cardinality rather than replacing it by q times that cardinality. -/
theorem real_dyadic_bins_sharp_upper {ι : Type*} (bins : ℕ → Finset ι) (u : ι → ℝ)
    (q amp S : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ amp) (hS : 0 ≤ S)
    (T : ℕ) (hT : 0 < T) (hzero : ((bins 0).card:ℝ) = S)
    (hcard : ∀ j ∈ range T, ((bins j).card:ℝ) ≤ q*S)
    (hcap : ∀ j ∈ range T, ∀ i ∈ bins j, |u i| ≤ 2*amp*(1/2:ℝ)^j) :
    (∑ j ∈ range T, ∑ i ∈ bins j, |u i|) ≤
      2*amp*S + 2*q*amp*S*(∑' j : ℕ, (1/2:ℝ)^(j+1)) ∧
    (∑ j ∈ range T, ∑ i ∈ bins j, (u i)^2) ≤
      4*amp^2*S + 4*q*amp^2*S*(∑' j : ℕ, (1/4:ℝ)^(j+1)) := by
  have h0T : 0 ∈ range T := mem_range.mpr hT
  have hm0 : (∑ i ∈ bins 0, |u i|) ≤ 2*amp*S := by
    have h := bin_mass_le (bins 0) u (2*amp) (by simpa using hcap 0 h0T)
    rw [hzero] at h
    nlinarith
  have hQ0 : (∑ i ∈ bins 0, (u i)^2) ≤ 4*amp^2*S := by
    have h := bin_energy_le (bins 0) u (2*amp) (by positivity) (by simpa using hcap 0 h0T)
    rw [hzero] at h
    nlinarith
  have hmj : ∀ j ∈ Ico 1 T, (∑ i ∈ bins j, |u i|) ≤ 2*q*amp*S*(1/2:ℝ)^j := by
    intro j hj
    have hjT := mem_range.mpr (mem_Ico.mp hj).2
    calc
      _ ≤ ((bins j).card:ℝ)*(2*amp*(1/2:ℝ)^j) := bin_mass_le _ _ _ (hcap j hjT)
      _ ≤ (q*S)*(2*amp*(1/2:ℝ)^j) := mul_le_mul_of_nonneg_right (hcard j hjT) (by positivity)
      _ = _ := by ring
  have hQj : ∀ j ∈ Ico 1 T, (∑ i ∈ bins j, (u i)^2) ≤ 4*q*amp^2*S*(1/4:ℝ)^j := by
    intro j hj
    have hjT := mem_range.mpr (mem_Ico.mp hj).2
    have hp : ((1/2:ℝ)^j)^2 = (1/4:ℝ)^j := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    calc
      _ ≤ ((bins j).card:ℝ)*(2*amp*(1/2:ℝ)^j)^2 := bin_energy_le _ _ _ (by positivity) (hcap j hjT)
      _ ≤ (q*S)*(2*amp*(1/2:ℝ)^j)^2 := mul_le_mul_of_nonneg_right (hcard j hjT) (sq_nonneg _)
      _ = _ := by simp only [mul_pow, hp]; ring
  have hmtail : (∑ j ∈ Ico 1 T, ∑ i ∈ bins j, |u i|) ≤ 2*q*amp*S := by
    have h := finite_geometric_domination _ (2*q*amp*S) (1/2) (by positivity)
      (by norm_num) (by norm_num) 1 T hmj
    convert h using 1 <;> ring
  have hQtail : (∑ j ∈ Ico 1 T, ∑ i ∈ bins j, (u i)^2) ≤ (4*q/3)*amp^2*S := by
    have h := finite_geometric_domination _ (4*q*amp^2*S) (1/4) (by positivity)
      (by norm_num) (by norm_num) 1 T hQj
    convert h using 1 <;> ring
  have hmsplit := sum_range_add_sum_Ico (fun j => ∑ i ∈ bins j, |u i|) (show 1 ≤ T by omega)
  have hQsplit := sum_range_add_sum_Ico (fun j => ∑ i ∈ bins j, (u i)^2) (show 1 ≤ T by omega)
  simp only [sum_range_one] at hmsplit hQsplit
  rw [(real_dyadic_series_values T).1, (real_dyadic_series_values T).2.1]
  constructor <;> nlinarith

theorem real_retained_group_sharp_estimates {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (t : ℕ) (tail : List ℕ)
    (hbase : (dyadicBin u amp t).Nonempty)
    (hsmall : ∀ s ∈ tail, ((dyadicBin u amp s).card : ℝ) < q * (dyadicBin u amp t).card)
    (T : ℕ) (hT : 0 < T) :
    let I := recordRetainedSupport u amp t tail T
    let S : ℝ := (dyadicBin u amp t).card
    let amp' := amp * (1 / 2 : ℝ)^(t+1)
    let m := ∑ i ∈ I, |u i|
    let Q := ∑ i ∈ I, (u i)^2
    m ≤ 2*amp'*S + 2*q*amp'*S*(∑' j : ℕ, (1/2:ℝ)^(j+1)) ∧
    Q ≤ 4*amp'^2*S + 4*q*amp'^2*S*(∑' j : ℕ, (1/4:ℝ)^(j+1)) := by
  classical
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  dsimp only
  let bins := recordOffsetBin u amp t tail
  let S : ℝ := (dyadicBin u amp t).card
  let amp' : ℝ := amp * (1 / 2 : ℝ)^(t+1)
  have hS : 0 < S := by
    dsimp [S]
    exact_mod_cast Finset.card_pos.mpr hbase
  have ha' : 0 < amp' := mul_pos ha (pow_pos (by norm_num) _)
  have hcard : ∀ j, ((bins j).card : ℝ) ≤ q * S := by
    intro j
    dsimp [bins, recordOffsetBin]
    split_ifs with hj
    · rcases List.mem_cons.mp hj with heq | hmem
      · rw [heq]
        change S ≤ q * S
        nlinarith
      · apply le_of_lt
        dsimp [S]
        exact hsmall (t+j) hmem
    · simp only [Finset.card_empty, Nat.cast_zero]
      nlinarith
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
  have hd : Set.PairwiseDisjoint (↑(Finset.range T) : Set ℕ) bins := by
    intro j hj k hk hne
    exact recordOffsetBin_disjoint u amp ha.le t tail j k hne
  have hm_eq : (∑ i ∈ recordRetainedSupport u amp t tail T, |u i|) =
      ∑ j ∈ Finset.range T, ∑ i ∈ bins j, |u i| := Finset.sum_biUnion hd
  have hQ_eq : (∑ i ∈ recordRetainedSupport u amp t tail T, (u i)^2) =
      ∑ j ∈ Finset.range T, ∑ i ∈ bins j, (u i)^2 := Finset.sum_biUnion hd
  rw [hm_eq, hQ_eq]
  exact real_dyadic_bins_sharp_upper bins u q amp' S hq0.le ha'.le hS.le T hT
    (by rw [hzero]) (fun j _ => hcard j) (fun j _ => hcap j)

#print axioms real_retained_group_sharp_estimates
#print axioms real_dyadic_series_values
#print axioms real_dyadic_bins_sharp_upper
end GaussianEllipsoidCandidate
namespace GaussianEllipsoidCandidate
open Finset

/-- Retained and omitted coordinates are disjoint globally, including across
records. The proof checks the offset cut after identifying the actual dyadic level. -/
theorem real_retained_omitted_disjoint {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T N : ℕ)
    (hflat : groups.flatten = dyadicRecordLevels u amp N)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g) :
    Disjoint (retainedGroupUnion u amp groups T)
      (groups.toFinset.biUnion fun g => recordOmittedSupport u amp (g.headD 0) g.tail T N) := by
  classical
  have hnodup : groups.flatten.Nodup := by
    rw [hflat]
    exact List.Nodup.filter _ List.nodup_range
  have hgroups := (List.nodup_flatten.mp hnodup).2
  letI : Std.Symm (List.Disjoint : List ℕ → List ℕ → Prop) := ⟨fun _ _ h => h.symm⟩
  apply Finset.disjoint_left.mpr
  intro i hiR hiO
  obtain ⟨g, hg, hiR⟩ := Finset.mem_biUnion.mp hiR
  obtain ⟨h, hh, hiO⟩ := Finset.mem_biUnion.mp hiO
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hiR
  obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hiO
  dsimp [recordOffsetBin] at hij hik
  split_ifs at hij with hgj
  · split_ifs at hik with hhk
    · have heq := dyadic_level_unique amp (u i) ha _ _
        ((mem_dyadicBin _ _ _ _).mp hij) ((mem_dyadicBin _ _ _ _).mp hik)
      by_cases hgh : g=h
      · subst h
        have hj' := mem_range.mp hj
        have hk' := (mem_Ico.mp hk).1
        omega
      · have hdis := hgroups.forall (List.mem_toFinset.mp hg) (List.mem_toFinset.mp hh) hgh
        have hgcons : g.headD 0 :: g.tail = g := by
          obtain ⟨a, atail, heq, _⟩ := hreg g (List.mem_toFinset.mp hg)
          subst g
          rfl
        have hhcons : h.headD 0 :: h.tail = h := by
          obtain ⟨a, atail, heq, _⟩ := hreg h (List.mem_toFinset.mp hh)
          subst h
          rfl
        rw [hgcons] at hgj
        rw [hhcons, ← heq] at hhk
        exact List.disjoint_left.mp hdis hgj hhk
    · simp at hik
  · simp at hij

/-- Coverage from the finite partition gives the paper's exact omitted vector
identity W=u-V=sum_r W_r, using the same constructed groups and cutoff. -/
theorem real_omittedGroupVector_eq_residual {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp)
    (groups : List (List ℕ)) (T N : ℕ)
    (hflat : groups.flatten = dyadicRecordLevels u amp N)
    (hcover0 : ∀ i, u i ≠ 0 ↔ ∃ t ∈ range N, i ∈ dyadicBin u amp t)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g) :
    u-retainedGroupVector u amp groups T =
      ∑ g ∈ groups.toFinset,
        GaussianEllipsoid.Dyadic.restrict u
          (recordOmittedSupport u amp (g.headD 0) g.tail T N) := by
  classical
  let O : List ℕ → Finset ι := fun g => recordOmittedSupport u amp (g.headD 0) g.tail T N
  have hnodup : groups.flatten.Nodup := by
    rw [hflat]
    exact List.Nodup.filter _ List.nodup_range
  have hO : Set.PairwiseDisjoint (↑groups.toFinset : Set (List ℕ)) O := by
    apply dyadic_group_supports_disjoint u amp ha.le groups (List.nodup_flatten.mp hnodup).2 O
    intro g hg i hi
    obtain ⟨t, tail, heq, _⟩ := hreg g hg
    subst g
    exact omitted_mem_level u amp t tail T N i hi
  have hcover : ∀ i, u i ≠ 0 → i ∈ retainedGroupUnion u amp groups T ∨ i ∈ groups.toFinset.biUnion O := by
    intro i hi
    obtain ⟨s, hsN, his⟩ := (hcover0 i).mp hi
    have hsflat : s ∈ groups.flatten := by
      rw [hflat]
      exact (mem_dyadicRecordLevels u amp N s).mpr ⟨mem_range.mp hsN, ⟨i, his⟩⟩
    obtain ⟨g, hg, hsg⟩ := List.mem_flatten.mp hsflat
    obtain ⟨t, tail, heq, _⟩ := hreg g hg
    subst g
    have hbounds := real_actual_group_level_bounds u amp groups N t tail hflat hg
    have hts := hbounds.1 s hsg
    have hNs := hbounds.2 s hsg
    have heq : t+(s-t)=s := by omega
    by_cases hj : s-t<T
    · left
      apply mem_biUnion.mpr
      refine ⟨t::tail, List.mem_toFinset.mpr hg, ?_⟩
      apply mem_biUnion.mpr
      exact ⟨s-t, mem_range.mpr hj, by simpa [recordOffsetBin, heq, hsg] using his⟩
    · right
      apply mem_biUnion.mpr
      refine ⟨t::tail, List.mem_toFinset.mpr hg, ?_⟩
      apply mem_biUnion.mpr
      exact ⟨s-t, mem_Ico.mpr ⟨by omega, by omega⟩,
        by simpa [recordOffsetBin, heq, hsg] using his⟩
  have hdis := real_retained_omitted_disjoint q u amp ha.le groups T N hflat hreg
  have heq : u-retainedGroupVector u amp groups T =
      fun i => if i ∈ groups.toFinset.biUnion O then u i else 0 := by
    funext i
    change u i - (if i ∈ retainedGroupUnion u amp groups T then u i else 0) = _
    by_cases hR : i ∈ retainedGroupUnion u amp groups T
    · have hnO : i ∉ groups.toFinset.biUnion O := fun hO => Finset.disjoint_left.mp hdis hR hO
      simp [hR, hnO]
    · by_cases hOi : i ∈ groups.toFinset.biUnion O
      · simp [hR, hOi]
      · have hz : u i = 0 := by
          by_contra hn
          exact (hcover i hn).elim hR hOi
        simp [hR, hOi, hz]
  rw [heq]
  exact real_restrict_union_sum u groups.toFinset O hO

#print axioms real_retained_omitted_disjoint
#print axioms real_omittedGroupVector_eq_residual
end GaussianEllipsoidCandidate

namespace GaussianEllipsoidCandidate
open Finset

/-- Exact arbitrary-q energy–mass relation for the original indexed retained
support, ready for the rank-aware martingale-variance consumer. -/
theorem real_actual_group_energy_mass_product {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (r : ℕ) (hr : r < groups.length) :
    (∑ i ∈ dyadicGroupSupport u amp groups T r, (u i)^2) *
      dyadicGroupScale u amp groups r ≤
        (16*q/3) * (dyadicGroupMass u amp groups T r)^2 := by
  obtain ⟨t, tail, heq, hS, ha, hklo, hkhi, hmlo, hmhi, hQlo, hQhi,
    hm, hQ, hRlo, hRhi, henergy, hcap, htail⟩ := hreg groups[r] (List.getElem_mem hr)
  have hh := (le_div_iff₀ hS).mp henergy
  simpa only [dyadicGroupSupport, dyadicGroupScale, dyadicGroupMass,
    List.getElem?_eq_getElem hr, Option.getD_some, heq, List.headD_cons, List.tail_cons] using hh

#print axioms real_actual_group_energy_mass_product
end GaussianEllipsoidCandidate

namespace GaussianEllipsoidCandidate
open Finset

/-- Literal omitted-mass geometric-series display and its evaluated constant. -/
theorem real_record_omitted_series {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (t : ℕ) (tail : List ℕ)
    (hsmall : ∀ s ∈ tail, ((dyadicBin u amp s).card:ℝ) < q*(dyadicBin u amp t).card)
    (T N : ℕ) :
    let a := amp*(1/2:ℝ)^(t+1)
    let S : ℝ := (dyadicBin u amp t).card
    let W := GaussianEllipsoid.Dyadic.restrict u (recordOmittedSupport u amp t tail T N)
    coefficientMass W ≤ 2*q*a*S*(∑' j : ℕ, (1/2:ℝ)^(T+j)) ∧
    2*q*a*S*(∑' j : ℕ, (1/2:ℝ)^(T+j)) = 4*q*(1/2:ℝ)^T*a*S := by
  classical
  dsimp only
  have hm : coefficientMass (GaussianEllipsoid.Dyadic.restrict u (recordOmittedSupport u amp t tail T N)) =
      ∑ i ∈ recordOmittedSupport u amp t tail T N, |u i| := by
    simp [coefficientMass, GaussianEllipsoid.Dyadic.restrict, apply_ite abs]
  rw [hm, (real_dyadic_series_values T).2.2]
  constructor
  · convert real_record_omitted_mass q hq u amp ha t tail hsmall T N using 1 <;> ring
  · ring

/-- Complete source-quantified deterministic constructor, including u=0 and
lambda_max=||u||_infinity. The greedy certificate fixes the first-later selection,
not merely a relaxed growth condition. The remaining public bridge theorems
identify its vectors, norms, supports, and cumulative sums exactly. -/
theorem real_paper_dyadic_decomposition {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1 < q) (u : ι → ℝ) (T : ℕ) (hT : 0 < T) :
    ∃ N : ℕ, ∃ groups : List (List ℕ), 0 < N ∧
      (u=0 → groups=[]) ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ range N, i ∈ dyadicBin u ‖u‖ t) ∧
      (∀ t, N ≤ t → dyadicBin u ‖u‖ t = ∅) ∧
      groups.flatten = dyadicRecordLevels u ‖u‖ N ∧
      (∀ g ∈ groups, RealRegularRetainedGroup q u ‖u‖ T g) ∧
      groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
        fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) ∧
      coefficientMass (u-retainedGroupVector u ‖u‖ groups T) ≤
        4*q*(1/2:ℝ)^T*coefficientMass u ∧
      GaussianEllipsoid.PaperRealRecord.RecordGrouping q
        (fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) (dyadicRecordLevels u ‖u‖ N) groups := by
  classical
  by_cases hu : u=0
  · subst u
    have hbin : ∀ t, dyadicBin (0 : ι → ℝ) ‖(0 : ι → ℝ)‖ t = ∅ := by
      intro t
      simp [dyadicBin]
    have hlev : dyadicRecordLevels (0 : ι → ℝ) ‖(0 : ι → ℝ)‖ 1 = [] := by
      simp [dyadicRecordLevels, dyadicBin]
    refine ⟨1, [], by decide, by simp, ?_, ?_, ?_, by simp, by simp, ?_, ?_⟩
    · intro i
      simp [dyadicBin]
    · intro t ht
      exact hbin t
    · simpa using hlev.symm
    · simp [retainedGroupVector, retainedGroupUnion, coefficientMass]
    · rw [hlev]
      exact GaussianEllipsoid.PaperRealRecord.RecordGrouping.nil
  · have ha : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcap : ∀ i, |u i| ≤ ‖u‖ := by
      intro i
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
    obtain ⟨N, groups, hN, hcover, hempty, hflat, hreg, hchain, hcoord, herror, hgreedy⟩ :=
      exists_real_global_dyadic_retention q hq u ‖u‖ ha hcap T hT
    exact ⟨N, groups, hN, fun hz => (hu hz).elim, hcover, hempty, hflat, hreg, hchain, herror, hgreedy⟩

#print axioms real_record_omitted_series
#print axioms real_paper_dyadic_decomposition
end GaussianEllipsoidCandidate

namespace GaussianEllipsoidCandidate
open Finset
/-- Membership in a concrete retained group identifies an original dyadic
level in exactly that record group. -/
theorem real_actual_group_support_mem_level {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (r : ℕ) (hr : r < groups.length) (i : ι)
    (hi : i ∈ dyadicGroupSupport u amp groups T r) :
    ∃ t ∈ groups[r], i ∈ dyadicBin u amp t := by
  obtain ⟨t, tail, heq, _⟩ := hreg groups[r] (List.getElem_mem hr)
  have hi' : i ∈ recordRetainedSupport u amp t tail T := by
    simpa only [dyadicGroupSupport, List.getElem?_eq_getElem hr,
      Option.getD_some, heq, List.headD_cons, List.tail_cons] using hi
  rw [heq]
  exact retained_mem_level u amp t tail T i hi'

/-- Indexed actual retained supports are pairwise disjoint. -/
theorem real_actual_group_supports_pairwise {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup) (n : ℕ) (hn : n ≤ groups.length) :
    Set.PairwiseDisjoint (↑(range n) : Set ℕ) (dyadicGroupSupport u amp groups T) := by
  have hp := (List.nodup_flatten.mp hflat).2
  intro r hr s hs hne
  have hr' : r < groups.length := lt_of_lt_of_le (mem_range.mp hr) hn
  have hs' : s < groups.length := lt_of_lt_of_le (mem_range.mp hs) hn
  have hdis : List.Disjoint groups[r] groups[s] := by
    rcases lt_or_gt_of_ne hne with hrs | hsr
    · exact List.pairwise_iff_getElem.mp hp r s hr' hs' hrs
    · exact (List.pairwise_iff_getElem.mp hp s r hs' hr' hsr).symm
  apply Finset.disjoint_left.mpr
  intro i hir his
  obtain ⟨t, htr, hit⟩ := real_actual_group_support_mem_level q u amp groups T hreg r hr' i hir
  obtain ⟨v, hvs, hiv⟩ := real_actual_group_support_mem_level q u amp groups T hreg s hs' i his
  have heq := dyadic_level_unique amp (u i) ha t v
    ((mem_dyadicBin u amp t i).mp hit) ((mem_dyadicBin u amp v i).mp hiv)
  subst v
  exact List.disjoint_left.mp hdis htr hvs

/-- Disjoint actual groups partition the retained l1 mass exactly. -/
theorem real_actual_group_mass_sum {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup) :
    coefficientMass (retainedGroupVector u amp groups T) =
      ∑ r ∈ range groups.length, dyadicGroupMass u amp groups T r := by
  classical
  have hmass : coefficientMass (retainedGroupVector u amp groups T) =
      ∑ i ∈ retainedGroupUnion u amp groups T, |u i| := by
    classical
    simp only [coefficientMass, retainedGroupVector]
    simp_rw [apply_ite abs]
    simp
  rw [hmass, retainedGroupUnion_eq_indexed, indexedGroupUnion,
    sum_biUnion (real_actual_group_supports_pairwise q u amp ha groups T hreg hflat groups.length le_rfl)]
  rfl

/-- The paper's indexed sum of V_r agrees with the constructed retained vector. -/
theorem real_retainedGroupVector_eq_indexed_sum {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup) :
    retainedGroupVector u amp groups T =
      ∑ r ∈ range groups.length, GaussianEllipsoid.Dyadic.restrict u
        (dyadicGroupSupport u amp groups T r) := by
  classical
  unfold retainedGroupVector
  rw [retainedGroupUnion_eq_indexed]
  funext i
  have hsum := real_restrict_union_sum u (range groups.length) _
    (real_actual_group_supports_pairwise q u amp ha groups T hreg hflat groups.length le_rfl)
  calc
    _ = (if i ∈ (range groups.length).biUnion (dyadicGroupSupport u amp groups T)
        then u i else 0) := by rfl
    _ = ∑ r ∈ range groups.length,
        (if i ∈ dyadicGroupSupport u amp groups T r then u i else 0) := by
      simpa only [Finset.sum_apply] using congrFun hsum i
    _ = _ := by
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hi : i ∈ dyadicGroupSupport u amp groups T r <;>
        simp [GaussianEllipsoid.Dyadic.restrict, hi]

#print axioms real_actual_group_support_mem_level
#print axioms real_actual_group_supports_pairwise
#print axioms real_actual_group_mass_sum
#print axioms real_retainedGroupVector_eq_indexed_sum
end GaussianEllipsoidCandidate

namespace GaussianEllipsoidCandidate
open Finset

/-- A contiguous block of a strictly increasing level list is exactly the
half-open interval between its head and the next block's head, among present levels. -/
theorem real_list_block_interval (pre : List ℕ) (t : ℕ) (tail post : List ℕ)
    (hsort : (pre ++ ((t::tail) ++ post)).Pairwise (fun a b => a < b))
    (s : ℕ) (hs : s ∈ pre ++ ((t::tail) ++ post)) :
    s ∈ t::tail ↔ t ≤ s ∧ ∀ v ∈ post.head?, s < v := by
  have hp := List.pairwise_append.mp hsort
  have hgp := List.pairwise_append.mp hp.2.1
  constructor
  · intro hsg
    constructor
    · rcases List.mem_cons.mp hsg with heq | hst
      · omega
      · exact ((List.pairwise_cons.mp hgp.1).1 s hst).le
    · intro v hv
      exact hgp.2.2 s hsg v (List.mem_of_mem_head? hv)
  · rintro ⟨hts, hnext⟩
    rcases List.mem_append.mp hs with hpre | hrest
    · have hst := hp.2.2 s hpre t (List.mem_append_left _ (by simp))
      omega
    · rcases List.mem_append.mp hrest with hg | hpost
      · exact hg
      · cases post with
        | nil => simp at hpost
        | cons v vs =>
          have hsv : s < v := hnext v (by simp)
          have hvs : v ≤ s := by
            rcases List.mem_cons.mp hpost with heq | hmem
            · omega
            · exact ((List.pairwise_cons.mp hgp.2.1).1 s hmem).le
          omega

/-- Equality of coordinate unions only requires equality of level selectors
on nonempty bins. Thus ignored empty levels and an infinite final interval
have no effect on the source vector. -/
theorem real_levelCoords_congr {ι : Type*} [Fintype ι]
    (bins : ℕ → Finset ι) (A B : Set ℕ)
    (h : ∀ t, (bins t).Nonempty → (t∈A ↔ t∈B)) :
    GaussianEllipsoid.Dyadic.levelCoords bins A = GaussianEllipsoid.Dyadic.levelCoords bins B := by
  classical
  ext i
  simp only [GaussianEllipsoid.Dyadic.mem_levelCoords]
  constructor
  · rintro ⟨t, ht, hi⟩
    exact ⟨t, (h t ⟨i,hi⟩).mp ht, hi⟩
  · rintro ⟨t, ht, hi⟩
    exact ⟨t, (h t ⟨i,hi⟩).mpr ht, hi⟩

/-- Exact interval representation of the actual list groups. `post.flatten.head?`
is the next selected level; for the terminal group it is none, so the upper
endpoint condition is vacuous, exactly t_(R+1)=infinity. -/
theorem real_actual_group_interval {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (N t : ℕ) (tail : List ℕ)
    (pre post : List (List ℕ))
    (hflat : (pre ++ (t::tail)::post).flatten = dyadicRecordLevels u amp N)
    (hempty : ∀ s, N ≤ s → dyadicBin u amp s = ∅)
    (s : ℕ) (hs : (dyadicBin u amp s).Nonempty) :
    s ∈ t :: tail ↔ t ≤ s ∧ ∀ v ∈ post.flatten.head?, s < v := by
  have hsN : s < N := by
    by_contra hn
    have hh := hempty s (by omega)
    rw [hh] at hs
    exact Finset.not_nonempty_empty hs
  have hsort : (pre.flatten ++ ((t::tail) ++ post.flatten)).Pairwise (fun a b : ℕ => a < b) := by
    have hh : (dyadicRecordLevels u amp N).Pairwise (fun a b : ℕ => a < b) :=
      List.Pairwise.filter _ List.pairwise_lt_range
    rw [← hflat] at hh
    simpa only [List.flatten_append, List.flatten_cons] using hh
  have hmem : s ∈ pre.flatten ++ ((t::tail) ++ post.flatten) := by
    have hh := (mem_dyadicRecordLevels u amp N s).mpr ⟨hsN,hs⟩
    rw [← hflat] at hh
    simpa only [List.flatten_append, List.flatten_cons] using hh
  exact real_list_block_interval pre.flatten t tail post.flatten hsort s hmem

/-- The finite-list retained and omitted supports equal the paper's half-open
record-interval supports, even with empty levels and an unbounded last interval. -/
theorem real_actual_interval_supports {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (N t T : ℕ) (tail : List ℕ)
    (pre post : List (List ℕ))
    (hflat : (pre ++ (t::tail)::post).flatten = dyadicRecordLevels u amp N)
    (hempty : ∀ s, N ≤ s → dyadicBin u amp s = ∅) :
    let G : Set ℕ := {s | t ≤ s ∧ ∀ v ∈ post.flatten.head?, s < v}
    recordRetainedSupport u amp t tail T =
      GaussianEllipsoid.Dyadic.retainedCoords (GaussianEllipsoid.Dyadic.bin u amp) G t T ∧
    recordOmittedSupport u amp t tail T N =
      GaussianEllipsoid.Dyadic.omittedCoords (GaussianEllipsoid.Dyadic.bin u amp) G t T := by
  have hg : t::tail ∈ pre ++ (t::tail)::post := List.mem_append_cons_self
  have hb := real_actual_group_level_bounds u amp _ N t tail hflat hg
  dsimp only
  rw [real_retainedSupport_eq_paper_coords u amp t tail T hb.1,
    real_omittedSupport_eq_paper_coords u amp t tail T N hb.1 hb.2]
  constructor
  · unfold GaussianEllipsoid.Dyadic.retainedCoords
    apply real_levelCoords_congr
    intro s hs
    have hs' : (dyadicBin u amp s).Nonempty := by rwa [real_dyadicBin_eq_paper_bin]
    exact and_congr_left (fun _ => real_actual_group_interval u amp N t tail pre post hflat hempty s hs')
  · unfold GaussianEllipsoid.Dyadic.omittedCoords
    apply real_levelCoords_congr
    intro s hs
    have hs' : (dyadicBin u amp s).Nonempty := by rwa [real_dyadicBin_eq_paper_bin]
    exact and_congr_left (fun _ => real_actual_group_interval u amp N t tail pre post hflat hempty s hs')

#print axioms real_list_block_interval
#print axioms real_levelCoords_congr
#print axioms real_actual_group_interval
#print axioms real_actual_interval_supports
end GaussianEllipsoidCandidate

namespace GaussianEllipsoidCandidate
open Finset

/-- Nat-power notation used here is exactly the paper's negative dyadic power. -/
theorem real_half_pow_eq_negative_two_pow (T : ℕ) :
    (1/2:ℝ)^T = (2:ℝ)^(-(T:ℤ)) := by
  simp [zpow_neg, inv_pow, one_div]

/-- The list representation's amplitude equals the source's division representation. -/
theorem real_record_amplitude_eq (amp : ℝ) (t : ℕ) :
    amp*(1/2:ℝ)^(t+1) = GaussianEllipsoid.Dyadic.baseScale amp t := by
  simp [GaussianEllipsoid.Dyadic.baseScale, div_pow, div_eq_mul_inv]

/-- Exact finite-support cardinality representation of k_r. -/
theorem realRecordVector_finite_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (t : ℕ) (tail : List ℕ) (T : ℕ) :
    GaussianEllipsoid.Dyadic.support (realRecordVector u amp t tail T) =
      recordRetainedSupport u amp t tail T := by
  ext i
  have h := Set.ext_iff.mp (realRecordVector_support u amp ha t tail T) i
  simpa only [GaussianEllipsoid.Dyadic.mem_support, Function.mem_support, Finset.mem_coe] using h

/-- Base coefficients have the strict lower and weak upper endpoints stated in the paper. -/
theorem real_record_base_amplitudes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (i : ι) (hi : i∈dyadicBin u amp t) :
    amp*(1/2:ℝ)^(t+1) < |u i| ∧ |u i| ≤ 2*(amp*(1/2:ℝ)^(t+1)) := by
  rw [real_record_amplitude_eq]
  apply GaussianEllipsoid.Dyadic.base_bin_amplitude
  rwa [← real_dyadicBin_eq_paper_bin]

#print axioms real_half_pow_eq_negative_two_pow
#print axioms real_record_amplitude_eq
#print axioms realRecordVector_finite_support
#print axioms real_record_base_amplitudes
end GaussianEllipsoidCandidate

namespace GaussianEllipsoidCandidate
/-- The middle expressions in the source's displayed mass and energy chains
are themselves bounded by exactly 4q and16q/3, respectively. -/
theorem real_geometric_budget_endpoints (q a S : ℝ) (hq : 1 < q)
    (ha : 0 ≤ a) (hS : 0 ≤ S) :
    2*a*S + 2*q*a*S*(∑' j : ℕ, (1/2:ℝ)^(j+1)) ≤ 4*q*a*S ∧
    4*a^2*S + 4*q*a^2*S*(∑' j : ℕ, (1/4:ℝ)^(j+1)) ≤ (16*q/3)*a^2*S := by
  rw [(real_dyadic_series_values 0).1, (real_dyadic_series_values 0).2.1]
  have hm := mul_le_mul_of_nonneg_right hq.le (mul_nonneg ha hS)
  have hQ := mul_le_mul_of_nonneg_right hq.le (mul_nonneg (sq_nonneg a) hS)
  constructor <;> nlinarith
#print axioms real_geometric_budget_endpoints
end GaussianEllipsoidCandidate

namespace GaussianEllipsoidCandidate

/-- At the later paper specialization q=2, the real-valued record certificate
is equivalent to the existing natural-cardinality certificate, without changing groups. -/
theorem real_recordGrouping_two_iff {α : Type*} (weight : α → ℕ)
    (xs : List α) (groups : List (List α)) :
    GaussianEllipsoid.PaperRealRecord.RecordGrouping 2 (fun a => (weight a:ℝ)) xs groups ↔
      RecordGrouping weight xs groups := by
  constructor
  · intro h
    induction h with
    | nil => exact RecordGrouping.nil
    | cons a pref rest groups small next rec ih =>
      apply RecordGrouping.cons a pref rest groups ?_ ?_ ih
      · intro b hb
        exact_mod_cast small b hb
      · intro b tail heq
        exact_mod_cast next b tail heq
  · intro h
    induction h with
    | nil => exact GaussianEllipsoid.PaperRealRecord.RecordGrouping.nil
    | cons a pref rest groups small next rec ih =>
      apply GaussianEllipsoid.PaperRealRecord.RecordGrouping.cons a pref rest groups ?_ ?_ ih
      · intro b hb
        exact_mod_cast small b hb
      · intro b tail heq
        exact_mod_cast next b tail heq

/-- Every retained-vector invariant is identical to the existing release's
invariant at q=2. Later specialized consumers can therefore reuse the same groups. -/
theorem real_regularRetainedGroup_two_iff {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (T : ℕ) (g : List ℕ) :
    RealRegularRetainedGroup 2 u amp T g ↔ RegularRetainedGroup u amp T g := by
  norm_num [RealRegularRetainedGroup, RegularRetainedGroup]

#print axioms real_recordGrouping_two_iff
#print axioms real_regularRetainedGroup_two_iff
end GaussianEllipsoidCandidate
