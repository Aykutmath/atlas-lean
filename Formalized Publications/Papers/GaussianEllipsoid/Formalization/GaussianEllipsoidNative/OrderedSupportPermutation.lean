import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
open Finset
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Deterministic cumulative support cardinality; repeated cuts encode empty groups. -/
def supportCut {n : ℕ} (G : ℕ → Finset (Fin n)) (k : ℕ) : ℕ :=
  ∑ j ∈ range k, (G j).card

@[simp] theorem supportCut_zero {n : ℕ} (G : ℕ → Finset (Fin n)) : supportCut G 0 = 0 := by
  simp [supportCut]

@[simp] theorem supportCut_succ {n : ℕ} (G : ℕ → Finset (Fin n)) (k : ℕ) :
    supportCut G (k+1) = supportCut G k + (G k).card := by
  exact sum_range_succ _ _

theorem supportCut_mono {n : ℕ} (G : ℕ → Finset (Fin n)) : Monotone (supportCut G) := by
  intro i j hij
  exact sum_le_sum_of_subset_of_nonneg (range_mono hij) (by intros; omega)

private def partitionMap {n m : ℕ} (G : ℕ → Finset (Fin n))
    (x : Σ j : Fin m, ↥(G j.val)) : Fin n := x.2.val

private theorem partitionMap_bijective {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (hc : ∀ i : Fin n, ∃ j < m, i ∈ G j) : Function.Bijective (partitionMap (m := m) G) := by
  constructor
  · rintro ⟨j,i⟩ ⟨k,l⟩ h
    have hval : i.val = l.val := h
    have hjk : j = k := by
      by_contra hne
      have hd' := hd (mem_range.mpr j.isLt) (mem_range.mpr k.isLt)
        (fun he => hne (Fin.ext he))
      exact (disjoint_left.mp hd') i.property (hval ▸ l.property)
    subst k
    congr
    exact Subtype.ext hval
  · intro i
    obtain ⟨j,hj,hij⟩ := hc i
    exact ⟨⟨⟨j,hj⟩,⟨i,hij⟩⟩,rfl⟩

private def partitionEquiv {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (hc : ∀ i : Fin n, ∃ j < m, i ∈ G j) :
    (Σ j : Fin m, ↥(G j.val)) ≃ Fin n :=
  Equiv.ofBijective _ (partitionMap_bijective G hd hc)

private theorem partition_card {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (hc : ∀ i : Fin n, ∃ j < m, i ∈ G j) :
    (∑ j : Fin m, (G j.val).card) = n := by
  simpa using Fintype.card_congr (partitionEquiv G hd hc)

private def partitionPermutation {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (hc : ∀ i : Fin n, ∃ j < m, i ∈ G j) : Equiv.Perm (Fin n) :=
  (((partitionEquiv G hd hc).symm.trans
    (Equiv.sigmaCongrRight fun j : Fin m => (G j.val).equivFin)).trans
    finSigmaFinEquiv).trans (finCongr (partition_card G hd hc))

private theorem partitionPermutation_val {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (hc : ∀ i : Fin n, ∃ j < m, i ∈ G j)
    (j : Fin m) (i : ↥(G j.val)) :
    (partitionPermutation G hd hc i.val).val =
      supportCut G j.val + ((G j.val).equivFin i).val := by
  have hp : (partitionEquiv G hd hc).symm i.val = ⟨j,i⟩ :=
    (partitionEquiv G hd hc).symm_apply_eq.mpr rfl
  simp only [partitionPermutation, Equiv.trans_apply, hp,
    Equiv.sigmaCongrRight_apply, finCongr_apply, Fin.coe_cast, finSigmaFinEquiv_apply]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => (G k).card) j.val

private theorem partitionPermutation_mem_iff {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (hc : ∀ i : Fin n, ∃ j < m, i ∈ G j) (j : ℕ) (hj : j < m) (i : Fin n) :
    i ∈ G j ↔ supportCut G j ≤ (partitionPermutation G hd hc i).val ∧
      (partitionPermutation G hd hc i).val < supportCut G (j+1) := by
  constructor
  · intro hi
    have hv := partitionPermutation_val G hd hc ⟨j,hj⟩ ⟨i,hi⟩
    have hh := ((G j).equivFin ⟨i,hi⟩).isLt
    rw [supportCut_succ]
    dsimp only at hv
    omega
  · rintro ⟨hlo,hhi⟩
    obtain ⟨k,hk,hik⟩ := hc i
    have hv := partitionPermutation_val G hd hc ⟨k,hk⟩ ⟨i,hik⟩
    have hh := ((G k).equivFin ⟨i,hik⟩).isLt
    dsimp only at hv
    have hklo : supportCut G k ≤ (partitionPermutation G hd hc i).val := by omega
    have hkhi : (partitionPermutation G hd hc i).val < supportCut G (k+1) := by
      rw [supportCut_succ]; omega
    have heq : j = k := by
      rcases lt_trichotomy j k with hlt | heq | hgt
      · have hmono : supportCut G (j+1) ≤ supportCut G k := supportCut_mono G (Nat.succ_le_of_lt hlt)
        omega
      · exact heq
      · have hmono : supportCut G (k+1) ≤ supportCut G j := supportCut_mono G (Nat.succ_le_of_lt hgt)
        omega
    simpa [heq] using hik


/-- Append every unused coordinate as one final block. -/
def completedSupports {n : ℕ} (G : ℕ → Finset (Fin n)) (m : ℕ) (j : ℕ) :
    Finset (Fin n) :=
  if j < m then G j else univ \ (range m).biUnion G

private theorem completedSupports_disjoint {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) :
    Set.PairwiseDisjoint (↑(range (m+1)) : Set ℕ) (completedSupports G m) := by
  intro j hj k hk hjk
  change Disjoint (completedSupports G m j) (completedSupports G m k)
  have hj' := mem_range.mp hj
  have hk' := mem_range.mp hk
  by_cases hjm : j < m <;> by_cases hkm : k < m
  · simpa [completedSupports, hjm, hkm] using hd (mem_range.mpr hjm) (mem_range.mpr hkm) hjk
  · simp only [completedSupports, hjm, hkm, if_true, if_false]
    apply disjoint_left.mpr
    intro i hi hcomp
    exact (mem_sdiff.mp hcomp).2 (mem_biUnion.mpr ⟨j,mem_range.mpr hjm,hi⟩)
  · simp only [completedSupports, hjm, hkm, if_true, if_false]
    apply disjoint_left.mpr
    intro i hcomp hi
    exact (mem_sdiff.mp hcomp).2 (mem_biUnion.mpr ⟨k,mem_range.mpr hkm,hi⟩)
  · omega

private theorem completedSupports_cover {n : ℕ} (G : ℕ → Finset (Fin n)) (m : ℕ) :
    ∀ i : Fin n, ∃ j < m+1, i ∈ completedSupports G m j := by
  intro i
  by_cases hi : i ∈ (range m).biUnion G
  · obtain ⟨j,hj,hij⟩ := mem_biUnion.mp hi
    have hj' := mem_range.mp hj
    exact ⟨j,by omega,by simpa [completedSupports,hj'] using hij⟩
  · exact ⟨m,by omega,by simp [completedSupports,hi]⟩

theorem completedSupports_cut {n : ℕ} (G : ℕ → Finset (Fin n)) (m k : ℕ) (hk : k ≤ m) :
    supportCut (completedSupports G m) k = supportCut G k := by
  apply sum_congr rfl
  intro j hj
  have hj' : j < m := lt_of_lt_of_le (mem_range.mp hj) hk
  simp [completedSupports,hj']

/-- The actual deterministic permutation from original coordinates to ordered
contiguous group positions. Empty groups are retained as zero-width intervals;
coordinates in no group are appended after the final cut. -/
def supportOrderPermutation {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) : Equiv.Perm (Fin n) :=
  partitionPermutation (completedSupports G m) (completedSupports_disjoint G hd)
    (completedSupports_cover G m)

/-- Exact support-membership characterization, including empty groups. -/
theorem supportOrderPermutation_mem_iff {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (j : ℕ) (hj : j < m) (i : Fin n) :
    i ∈ G j ↔ supportCut G j ≤ (supportOrderPermutation G hd i).val ∧
      (supportOrderPermutation G hd i).val < supportCut G (j+1) := by
  have hh := partitionPermutation_mem_iff (completedSupports G m)
    (completedSupports_disjoint G hd) (completedSupports_cover G m) j (by omega) i
  simpa only [supportOrderPermutation, completedSupports_cut G m j (by omega),
    completedSupports_cut G m (j+1) (by omega), completedSupports, hj, if_true] using hh

/-- Prefix unions become precisely the initial rows, so every actual cutoff
agrees with the sample-prefix filtration. -/
theorem supportOrderPermutation_prefix_iff {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (k : ℕ) (hk : k ≤ m) (i : Fin n) :
    i ∈ (range k).biUnion G ↔ (supportOrderPermutation G hd i).val < supportCut G k := by
  constructor
  · intro hi
    obtain ⟨j,hj,hij⟩ := mem_biUnion.mp hi
    have hj' := mem_range.mp hj
    have hpos := (supportOrderPermutation_mem_iff G hd j (by omega) i).mp hij
    exact lt_of_lt_of_le hpos.2 (supportCut_mono G (by omega))
  · intro hi
    obtain ⟨j,hj,hij⟩ := completedSupports_cover G m i
    have hpos := (partitionPermutation_mem_iff (completedSupports G m)
      (completedSupports_disjoint G hd) (completedSupports_cover G m) j hj i).mp hij
    have hcut : supportCut (completedSupports G m) k = supportCut G k :=
      completedSupports_cut G m k hk
    have hjk : j < k := by
      by_contra hn
      have hmono := supportCut_mono (completedSupports G m) (Nat.le_of_not_gt hn)
      have hposlo : supportCut (completedSupports G m) j ≤
          (supportOrderPermutation G hd i).val := hpos.1
      omega
    have hjm : j < m := by omega
    exact mem_biUnion.mpr ⟨j,mem_range.mpr hjk,by simpa [completedSupports,hjm] using hij⟩

/-- No grouped index extends beyond the ambient number of rows. -/
theorem supportCut_le_ambient {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) (k : ℕ) (hk : k ≤ m) :
    supportCut G k ≤ n := by
  have hc := partition_card (completedSupports G m)
    (completedSupports_disjoint G hd) (completedSupports_cover G m)
  have hc' : supportCut (completedSupports G m) (m+1) = n :=
    (Fin.sum_univ_eq_sum_range (fun j => (completedSupports G m j).card) (m+1)).symm.trans hc
  have hmono := supportCut_mono (completedSupports G m) (show k ≤ m+1 by omega)
  rw [completedSupports_cut G m k hk] at hmono
  omega

/-- Literal finite interval in the permuted row positions. -/
def supportInterval (n lo hi : ℕ) : Finset (Fin n) :=
  univ.filter fun i => lo ≤ i.val ∧ i.val < hi

/-- Exact group image as a finite contiguous interval. -/
theorem supportOrderPermutation_image_group {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) (j : ℕ) (hj : j < m) :
    (G j).image (supportOrderPermutation G hd) =
      supportInterval n (supportCut G j) (supportCut G (j+1)) := by
  ext i
  rw [mem_image]
  simp only [supportInterval,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact (supportOrderPermutation_mem_iff G hd j hj k).mp hk
  · intro hi
    refine ⟨(supportOrderPermutation G hd).symm i,?_,by simp⟩
    apply (supportOrderPermutation_mem_iff G hd j hj _).mpr
    simpa using hi

/-- Exact prefix image as a finite initial interval. -/
theorem supportOrderPermutation_image_prefix {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) (k : ℕ) (hk : k ≤ m) :
    ((range k).biUnion G).image (supportOrderPermutation G hd) =
      supportInterval n 0 (supportCut G k) := by
  ext i
  rw [mem_image]
  simp only [supportInterval,mem_filter,mem_univ,true_and,Nat.zero_le,true_and]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact (supportOrderPermutation_prefix_iff G hd k hk j).mp hj
  · intro hi
    refine ⟨(supportOrderPermutation G hd).symm i,?_,by simp⟩
    apply (supportOrderPermutation_prefix_iff G hd k hk _).mpr
    simpa using hi

/-- The prefix count is exactly its cut, with no multiplicity. -/
theorem support_prefix_card {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) (k : ℕ) (hk : k ≤ m) :
    ((range k).biUnion G).card = supportCut G k := by
  exact card_biUnion (fun i hi j hj hij => hd (mem_range.mpr
    (lt_of_lt_of_le (mem_range.mp hi) hk)) (mem_range.mpr
      (lt_of_lt_of_le (mem_range.mp hj) hk)) hij)

/-- Empty groups are explicitly represented by equal consecutive cuts. -/
theorem supportCut_eq_iff_empty {n : ℕ} (G : ℕ → Finset (Fin n)) (j : ℕ) :
    supportCut G (j+1) = supportCut G j ↔ G j = ∅ := by
  rw [supportCut_succ]
  simp

/-- Every unused row lies after all selected groups, and conversely. -/
theorem supportOrderPermutation_unused_iff {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) (i : Fin n) :
    i ∉ (range m).biUnion G ↔ supportCut G m ≤ (supportOrderPermutation G hd i).val := by
  rw [supportOrderPermutation_prefix_iff G hd m le_rfl]
  exact not_lt


/-- Any consecutive run of actual groups becomes one contiguous interval. -/
theorem supportOrderPermutation_run_iff {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (p q : ℕ) (hpq : p ≤ q) (hq : q ≤ m) (i : Fin n) :
    i ∈ (Ico p q).biUnion G ↔ supportCut G p ≤ (supportOrderPermutation G hd i).val ∧
      (supportOrderPermutation G hd i).val < supportCut G q := by
  constructor
  · intro hi
    obtain ⟨j,hj,hij⟩ := mem_biUnion.mp hi
    obtain ⟨hpj,hjq⟩ := mem_Ico.mp hj
    have hpos := (supportOrderPermutation_mem_iff G hd j (by omega) i).mp hij
    exact ⟨(supportCut_mono G hpj).trans hpos.1,
      hpos.2.trans_le (supportCut_mono G (by omega))⟩
  · rintro ⟨hlo,hhi⟩
    obtain ⟨j,hj,hij⟩ := mem_biUnion.mp
      ((supportOrderPermutation_prefix_iff G hd q hq i).mpr hhi)
    have hjq := mem_range.mp hj
    have hpos := (supportOrderPermutation_mem_iff G hd j (by omega) i).mp hij
    have hpj : p ≤ j := by
      by_contra hn
      have hmono : supportCut G (j+1) ≤ supportCut G p := supportCut_mono G (by omega)
      omega
    exact mem_biUnion.mpr ⟨j,mem_Ico.mpr ⟨hpj,hjq⟩,hij⟩

/-- Exact image of a consecutive run, useful for sparse-prefix and late cutoffs. -/
theorem supportOrderPermutation_image_run {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (p q : ℕ) (hpq : p ≤ q) (hq : q ≤ m) :
    ((Ico p q).biUnion G).image (supportOrderPermutation G hd) =
      supportInterval n (supportCut G p) (supportCut G q) := by
  ext i
  rw [mem_image]
  simp only [supportInterval,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact (supportOrderPermutation_run_iff G hd p q hpq hq j).mp hj
  · intro hi
    refine ⟨(supportOrderPermutation G hd).symm i,?_,by simp⟩
    apply (supportOrderPermutation_run_iff G hd p q hpq hq _).mpr
    simpa using hi

/-- The consecutive interval endpoints satisfy the separated-block API. -/
theorem supportCut_separated {n m : ℕ} (G : ℕ → Finset (Fin n))
    (i j : Fin m) (hij : i ≠ j) :
    supportCut G (i.val+1) ≤ supportCut G j.val ∨
      supportCut G (j.val+1) ≤ supportCut G i.val := by
  rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
  · exact Or.inl (supportCut_mono G (by omega))
  · exact Or.inr (supportCut_mono G (by omega))

/-- Group intervals have exactly the original group's number of rows. -/
theorem supportInterval_card_group {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) (j : ℕ) (hj : j < m) :
    (supportInterval n (supportCut G j) (supportCut G (j+1))).card = (G j).card := by
  rw [← supportOrderPermutation_image_group G hd j hj]
  exact card_image_of_injective _ (supportOrderPermutation G hd).injective

/-- Prefix intervals have exactly the prefix support size. -/
theorem supportInterval_card_prefix {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) (k : ℕ) (hk : k ≤ m) :
    (supportInterval n 0 (supportCut G k)).card = supportCut G k := by
  rw [← supportOrderPermutation_image_prefix G hd k hk,
    card_image_of_injective _ (supportOrderPermutation G hd).injective,
    support_prefix_card G hd k hk]

end GaussianEllipsoidCandidate
