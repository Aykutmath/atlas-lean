import OrderedSupportPermutation
import PrefixWitnessDecomposition

noncomputable section
open Finset GaussianEllipsoid
namespace GaussianEllipsoidCandidate

/-- One merged sparse prefix together with each later captured group. -/
abbrev CapturedBlockIndex (p q : ℕ) := Option ↥(Ico p q)

def capturedBlockLo {n : ℕ} (G : ℕ → Finset (Fin n)) (p q : ℕ) : CapturedBlockIndex p q → ℕ
  | none => 0
  | some r => supportCut G r.val

def capturedBlockHi {n : ℕ} (G : ℕ → Finset (Fin n)) (p q : ℕ) : CapturedBlockIndex p q → ℕ
  | none => supportCut G p
  | some r => supportCut G (r.val+1)

theorem capturedBlock_ordered {n : ℕ} (G : ℕ → Finset (Fin n)) (p q : ℕ) :
    ∀ j, capturedBlockLo G p q j ≤ capturedBlockHi G p q j := by
  intro j
  cases j with
  | none => exact Nat.zero_le _
  | some r => exact supportCut_mono G (Nat.le_succ r.val)

theorem capturedBlock_first {n : ℕ} (G : ℕ → Finset (Fin n)) (p q : ℕ) :
    ∀ j, supportCut G p ≤ capturedBlockHi G p q j := by
  intro j
  cases j with
  | none => exact le_rfl
  | some r =>
    exact supportCut_mono G (by have := (mem_Ico.mp r.property).1; omega)

theorem capturedBlock_separated {n : ℕ} (G : ℕ → Finset (Fin n)) (p q : ℕ) :
    ∀ i j, i ≠ j → capturedBlockHi G p q i ≤ capturedBlockLo G p q j ∨
      capturedBlockHi G p q j ≤ capturedBlockLo G p q i := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some r => exact Or.inl (supportCut_mono G (mem_Ico.mp r.property).1)
  | some r =>
    cases j with
    | none => exact Or.inr (supportCut_mono G (mem_Ico.mp r.property).1)
    | some s =>
      have hne : r.val ≠ s.val := by intro he; exact hij (congrArg some (Subtype.ext he))
      rcases lt_or_gt_of_ne hne with hrs | hsr
      · exact Or.inl (supportCut_mono G (by omega))
      · exact Or.inr (supportCut_mono G (by omega))

theorem capturedBlock_bounded {n m : ℕ} (G : ℕ → Finset (Fin n))
    (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G) (p q : ℕ)
    (hpq : p ≤ q) (hqm : q ≤ m) :
    ∀ j, capturedBlockHi G p q j ≤ n := by
  intro j
  cases j with
  | none => exact supportCut_le_ambient G hd p (hpq.trans hqm)
  | some r =>
    exact supportCut_le_ambient G hd (r.val+1) (by have := (mem_Ico.mp r.property).2; omega)

/-- The mass attached to this actual block family sums to all captured mass. -/
theorem capturedBlock_mass_sum (m : ℕ → ℝ) (p q : ℕ) (hpq : p ≤ q) :
    (∑ j : CapturedBlockIndex p q, match j with
      | none => ∑ r ∈ range p, m r
      | some r => m r.val) = ∑ r ∈ range q, m r := by
  rw [Fintype.sum_option]
  have hs : (∑ r : ↥(Ico p q), m r.val) = ∑ r ∈ Ico p q, m r := by
    exact Finset.sum_attach (Ico p q) m
  rw [hs]
  exact sum_range_add_sum_Ico m hpq

/-- The diagonal-plus-cross inequality is now specialized to the precise
sparse-prefix/captured-block family constructed from actual supports. -/
theorem nuclear_lower_from_captured_blocks {n m r s : ℕ}
    (G : ℕ → Finset (Fin n)) (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (p q : ℕ) (hpq : p ≤ q) (hqm : q ≤ m) (u : Fin n → ℝ)
    (X : Fin n → Euclid s × Euclid r) :
    (∑ j : CapturedBlockIndex p q,
      spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock u X (capturedBlockLo G p q j) (capturedBlockHi G p q j)))) / 2 +
      prefixWitnessCross u (fun i => if i.val < supportCut G p then 0 else u i)
        (capturedBlockLo G p q) (capturedBlockHi G p q) X ≤
      spectralNuclearNorm (operatorFrobenius (bilinearSynthesis u X)) := by
  rw [prefixWitnessCross_mask_prefix u _ _ _ (capturedBlock_first G p q)]
  exact nuclear_lower_from_prefix_blocks u _ _ (capturedBlock_ordered G p q)
    (capturedBlock_bounded G hd p q hpq hqm) (capturedBlock_separated G p q) X

end GaussianEllipsoidCandidate
