module

/-
# Lemma 2.1 refinement: exactly two nonzero signed terms

Standalone form of the paper's "more precisely" clause in Lemma 2.1:
off the null set `cocycleNull Y`, either every signed indicator term
vanishes, or exactly two are nonzero — one equal to `1`, the other
to `-1`.  The alternating sum `cocycle_alternating_sum` is the
summed consequence; this module extracts the structural statement
itself, reusing the public line-analysis lemmas of `Cocycle.lean`.
-/

public import Section_2_Cocycle.Cocycle

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

/-- Pointwise refinement off the exceptional null set (`m ≥ 1`). -/
public theorem cocycle_term_structure {m : ℕ} (hm : 1 ≤ m)
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) (hxN : x ∉ cocycleNull Y) :
    (∀ r, cocycleSigma Y r * (cocycleSimplex Y r).indicator 1 x = 0) ∨
    ∃ a b : Fin (m + 2), a ≠ b ∧
      cocycleSigma Y a * (cocycleSimplex Y a).indicator 1 x = 1 ∧
      cocycleSigma Y b * (cocycleSimplex Y b).indicator 1 x = -1 ∧
      ∀ r, r ≠ a → r ≠ b →
        cocycleSigma Y r * (cocycleSimplex Y r).indicator 1 x = 0 := by
  by_cases hex : ∃ β0 : Fin (m + 2) → ℝ, (∀ s, 0 ≤ β0 s)
      ∧ ∑ s, β0 s = 1 ∧ (∑ s, β0 s • Y s) = x
  · obtain ⟨β0, hpos0, hsum0, hcomb0⟩ := hex
    by_cases hlam : ∃ r₀, cocycleLambda Y r₀ ≠ 0
    · obtain ⟨⟨rp, hrp⟩, ⟨rn, hrn⟩⟩ := cocycleLambda_sign_classes Y hlam
      have hP : (cocyclePos Y).Nonempty :=
        ⟨rp, Finset.mem_filter.mpr ⟨Finset.mem_univ rp, hrp⟩⟩
      have hN : (cocycleNeg Y).Nonempty :=
        ⟨rn, Finset.mem_filter.mpr ⟨Finset.mem_univ rn, hrn⟩⟩
      obtain ⟨rmin, hrminP, hrminT⟩ := cocycleTmin_attains Y β0 hP
      obtain ⟨rmax, hrmaxN, hrmaxT⟩ := cocycleTmax_attains Y β0 hN
      have hposmin : (0 : ℝ) < cocycleLambda Y rmin :=
        cocyclePos_mem Y rmin hrminP
      have hnegmax : cocycleLambda Y rmax < 0 :=
        cocycleNeg_mem Y rmax hrmaxN
      have hminneq : rmin ≠ rmax := by
        intro heq
        rw [heq] at hposmin
        linarith
      have hsigmin : cocycleSigma Y rmin = 1 := by
        rw [cocycleSigma_eq_sign_lambda]
        exact Real.sign_of_pos hposmin
      have hsigmax : cocycleSigma Y rmax = -1 := by
        rw [cocycleSigma_eq_sign_lambda]
        exact Real.sign_of_neg hnegmax
      have hindmin : (cocycleSimplex Y rmin).indicator
          (1 : EuclideanSpace ℝ (Fin m) → ℝ) x = (1 : ℝ) := by
        have hmem : x ∈ cocycleSimplex Y rmin := by
          rw [mem_cocycleSimplex_iff_Tmin Y x β0 hpos0 hsum0 hcomb0 hP hN
            rmin hrminP]
          exact hrminT
        simp only [Set.indicator_of_mem hmem 1, Pi.one_apply]
      have hindmax : (cocycleSimplex Y rmax).indicator
          (1 : EuclideanSpace ℝ (Fin m) → ℝ) x = (1 : ℝ) := by
        have hmem : x ∈ cocycleSimplex Y rmax := by
          rw [mem_cocycleSimplex_iff_Tmax Y x β0 hpos0 hsum0 hcomb0 hP hN
            rmax hrmaxN]
          exact hrmaxT
        simp only [Set.indicator_of_mem hmem 1, Pi.one_apply]
      refine Or.inr ⟨rmin, rmax, hminneq, ?_, ?_, ?_⟩
      · rw [hsigmin, hindmin, mul_one]
      · rw [hsigmax, hindmax, mul_one]
      · intro r hrmin hrmax
        by_cases hlamr : cocycleLambda Y r = 0
        · rw [cocycleSigma_eq_sign_lambda, hlamr, Real.sign_zero, zero_mul]
        · rcases lt_or_gt_of_ne hlamr with hneg | hpos
          · have hrN : r ∈ cocycleNeg Y :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ r, hneg⟩
            have hnot : x ∉ cocycleSimplex Y r := by
              rw [mem_cocycleSimplex_iff_Tmax Y x β0 hpos0 hsum0
                hcomb0 hP hN r hrN]
              intro hcon
              exact hrmax (cocycleNeg_attainer_unique hm Y x hxN β0
                hpos0 hsum0 hcomb0 hP hN rmax hrmaxN hrmaxT r hrN hcon)
            rw [Set.indicator_of_notMem hnot 1, mul_zero]
          · have hrP : r ∈ cocyclePos Y :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ r, hpos⟩
            have hnot : x ∉ cocycleSimplex Y r := by
              rw [mem_cocycleSimplex_iff_Tmin Y x β0 hpos0 hsum0
                hcomb0 hP hN r hrP]
              intro hcon
              exact hrmin (cocyclePos_attainer_unique hm Y x hxN β0
                hpos0 hsum0 hcomb0 hP hN rmin hrminP hrminT r hrP hcon)
            rw [Set.indicator_of_notMem hnot 1, mul_zero]
    · have hall : ∀ r, cocycleLambda Y r = 0 :=
        fun r => not_ne_iff.mp fun h => hlam ⟨r, h⟩
      refine Or.inl (fun r => ?_)
      rw [cocycleSigma_eq_sign_lambda, hall r, Real.sign_zero, zero_mul]
  · refine Or.inl (fun r => ?_)
    have hnot : x ∉ cocycleSimplex Y r := by
      intro hmem
      rw [mem_cocycleSimplex_iff] at hmem
      obtain ⟨β, hpos, hsum, hcomb, hr0⟩ := hmem
      exact hex ⟨β, hpos, hsum, hcomb⟩
    rw [Set.indicator_of_notMem hnot 1, mul_zero]

/-- Lemma 2.1, "more precisely" clause (a.e. form, `m ≥ 1`). -/
public theorem cocycle_exactly_two_nonzero {m : ℕ} (hm : 1 ≤ m)
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      (∀ r, cocycleSigma Y r * (cocycleSimplex Y r).indicator 1 x = 0) ∨
      ∃ a b : Fin (m + 2), a ≠ b ∧
        cocycleSigma Y a * (cocycleSimplex Y a).indicator 1 x = 1 ∧
        cocycleSigma Y b * (cocycleSimplex Y b).indicator 1 x = -1 ∧
        ∀ r, r ≠ a → r ≠ b →
          cocycleSigma Y r * (cocycleSimplex Y r).indicator 1 x = 0 := by
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      x ∉ cocycleNull Y :=
    measure_eq_zero_iff_ae_notMem.mp (volume_cocycleNull Y)
  filter_upwards [hae] with x hxN
  exact cocycle_term_structure hm Y x hxN

/-- Dimension-zero signed terms: the two terms are `1` and `-1`
everywhere (paper Lemma 2.1, `d = 1` case). -/
public theorem cocycle_dim1_terms (Y : Fin 2 → EuclideanSpace ℝ (Fin 0))
    (x : EuclideanSpace ℝ (Fin 0)) :
    cocycleSigma Y 0 * (cocycleSimplex Y 0).indicator 1 x = 1 ∧
    cocycleSigma Y 1 * (cocycleSimplex Y 1).indicator 1 x = -1 := by
  have hsig : ∀ r : Fin 2, cocycleSigma Y r = (-1) ^ (r.val) := by
    intro r
    simp only [cocycleSigma, cocycleDet, simDet_dim0, Real.sign_one, mul_one]
  have hind : ∀ r : Fin 2,
      (cocycleSimplex Y r).indicator (1 : EuclideanSpace ℝ (Fin 0) → ℝ) x
        = (1 : ℝ) := by
    intro r
    rw [cocycleSimplex_dim0]
    simp only [Set.indicator_of_mem (Set.mem_univ x) 1, Pi.one_apply]
  constructor
  · rw [hsig 0, hind 0]
    norm_num
  · rw [hsig 1, hind 1]
    norm_num

end HypercubeInequality
