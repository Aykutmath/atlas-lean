import OrderedSupportPermutation
import CanonicalGaussianPermutation

noncomputable section
open Finset MeasureTheory GaussianEllipsoid
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Row reindexing preserves any finite additive statistic. -/
theorem sum_permuteRows {ι : Type*} [Fintype ι] {M : Type*} [AddCommMonoid M]
    (e : Equiv.Perm ι) (f : ι → M) : ∑ i, permuteRows e f i = ∑ i, f i :=
  e.symm.sum_comp f

/-- The support of a coefficient vector is literally moved by the permutation. -/
theorem support_permuteRows {ι : Type*} (e : Equiv.Perm ι) (u : ι → ℝ) :
    Function.support (permuteRows e u) = e '' Function.support u := by
  ext i
  simp only [Function.mem_support, permuteRows, Set.mem_image]
  constructor
  · intro hi
    exact ⟨e.symm i,hi,by simp⟩
  · rintro ⟨j,hj,rfl⟩
    simpa using hj

/-- A permuted single-group coefficient vector is exactly an interval restriction. -/
theorem permuteRows_group_restriction {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (j : ℕ) (hj : j < m) (u : Fin n → ℝ) :
    permuteRows (supportOrderPermutation G hd) (fun i => if i ∈ G j then u i else 0) =
      fun i => if supportCut G j ≤ i.val ∧ i.val < supportCut G (j+1)
        then permuteRows (supportOrderPermutation G hd) u i else 0 := by
  funext i
  simp only [permuteRows]
  congr 1
  have hh := supportOrderPermutation_mem_iff G hd j hj
    ((supportOrderPermutation G hd).symm i)
  exact propext (by simpa using hh)

/-- A permuted run restriction is exactly its interval restriction. -/
theorem permuteRows_run_restriction {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (p q : ℕ) (hpq : p ≤ q) (hq : q ≤ m) (u : Fin n → ℝ) :
    permuteRows (supportOrderPermutation G hd)
      (fun i => if i ∈ (Ico p q).biUnion G then u i else 0) =
      fun i => if supportCut G p ≤ i.val ∧ i.val < supportCut G q
        then permuteRows (supportOrderPermutation G hd) u i else 0 := by
  funext i
  simp only [permuteRows]
  congr 1
  have hh := supportOrderPermutation_run_iff G hd p q hpq hq
    ((supportOrderPermutation G hd).symm i)
  exact propext (by simpa using hh)

/-- A permuted prefix restriction is exactly an initial-rows restriction. -/
theorem permuteRows_prefix_restriction {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (k : ℕ) (hk : k ≤ m) (u : Fin n → ℝ) :
    permuteRows (supportOrderPermutation G hd)
      (fun i => if i ∈ (range k).biUnion G then u i else 0) =
      fun i => if i.val < supportCut G k
        then permuteRows (supportOrderPermutation G hd) u i else 0 := by
  funext i
  simp only [permuteRows]
  congr 1
  have hh := supportOrderPermutation_prefix_iff G hd k hk
    ((supportOrderPermutation G hd).symm i)
  exact propext (by simpa using hh)

/-- Actual group synthesis equals synthesis on the corresponding reordered block. -/
theorem bilinearSynthesis_ordered_group {n m q r : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (j : ℕ) (hj : j < m) (u : Fin n → ℝ) (X : Fin n → Euclid q × Euclid r) :
    bilinearSynthesis
      (fun i => if supportCut G j ≤ i.val ∧ i.val < supportCut G (j+1)
        then permuteRows (supportOrderPermutation G hd) u i else 0)
      (permuteRows (supportOrderPermutation G hd) X) =
      bilinearSynthesis (fun i => if i ∈ G j then u i else 0) X := by
  rw [← permuteRows_group_restriction G hd j hj u]
  exact bilinearSynthesis_permuteRows _ _ _

/-- Actual consecutive-group synthesis equals synthesis on its reordered interval. -/
theorem bilinearSynthesis_ordered_run {n m q r : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (p s : ℕ) (hps : p ≤ s) (hs : s ≤ m) (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) :
    bilinearSynthesis
      (fun i => if supportCut G p ≤ i.val ∧ i.val < supportCut G s
        then permuteRows (supportOrderPermutation G hd) u i else 0)
      (permuteRows (supportOrderPermutation G hd) X) =
      bilinearSynthesis (fun i => if i ∈ (Ico p s).biUnion G then u i else 0) X := by
  rw [← permuteRows_run_restriction G hd p s hps hs u]
  exact bilinearSynthesis_permuteRows _ _ _

/-- Exact coefficient mass and squared-energy invariance needed by cross tails. -/
theorem permuteRows_abs_sq {n : ℕ} (e : Equiv.Perm (Fin n)) (u : Fin n → ℝ) :
    (∑ i, |permuteRows e u i|) = (∑ i, |u i|) ∧
      (∑ i, (permuteRows e u i)^2) = (∑ i, (u i)^2) :=
  ⟨e.symm.sum_comp (fun i => |u i|), e.symm.sum_comp (fun i => (u i)^2)⟩

end GaussianEllipsoidCandidate
