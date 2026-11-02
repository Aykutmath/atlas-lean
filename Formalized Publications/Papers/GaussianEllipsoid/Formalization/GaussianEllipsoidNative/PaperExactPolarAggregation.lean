import PaperExactCompensator
import CapturedBlockGeometry

noncomputable section
set_option maxHeartbeats 700000
open MeasureTheory Module GaussianEllipsoid GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperCanonicalPolar

theorem exactPrefixCross_eq_future_sum {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ) (X : Fin N → Euclid q × Euclid r) :
    exactPrefixCross u u lo hi X =
      ∑ j, prefixFuturePairing u X (hi j) (exactPrefixBlockWitness u X (lo j) (hi j)) := by
  unfold exactPrefixCross exactCompletedPrefix completedSupportedPrefix prefixFuturePairing
  simp only [ContinuousLinearMap.sum_apply,sum_inner,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Literal diagonal-plus-forward-cross identity. Exact canonical polar
attainment gives the complete block nuclear norm, with no fractional loss. -/
theorem exact_prefix_diagonal_cross_identity {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (X : Fin N → Euclid q × Euclid r) :
    (∑ j, spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock u X (lo j) (hi j)))) +
      exactPrefixCross u u lo hi X =
      ⟪operatorFrobenius (bilinearSynthesis u X),
        operatorFrobenius (∑ j,exactPrefixBlockWitness u X (lo j) (hi j))⟫_ℝ := by
  have hdiag (j : ι) :
      spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock u X (lo j) (hi j))) =
      ⟪operatorFrobenius (prefixBilinearSynthesis u X (hi j)),
        operatorFrobenius (exactPrefixBlockWitness u X (lo j) (hi j))⟫_ℝ := by
    have hp := exactPrefixBlockWitness_properties u X (hlo j)
    symm
    rw [inner_supported_eq_compressed (leftIncrement X (lo j) (hi j))
      (rightIncrement X (lo j) (hi j)) _ (exactPrefixBlockWitness u X (lo j) (hi j))
      (prefixSpanProjector_increment_selfAdjoint _ _ _)
      (prefixSpanProjector_increment_selfAdjoint _ _ _) hp.2.1]
    exact hp.2.2.1
  rw [exactPrefixCross_eq_future_sum,operatorFrobenius_sum,inner_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hdiag j]
  exact (synthesis_pairing_prefix_future u X (hi j)
    (exactPrefixBlockWitness u X (lo j) (hi j))).symm

theorem exact_nuclear_lower_from_prefix_blocks {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j) (hhi : ∀ j,hi j ≤ N)
    (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (X : Fin N → Euclid q × Euclid r) :
    (∑ j, spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock u X (lo j) (hi j)))) +
      exactPrefixCross u u lo hi X ≤ spectralNuclearNorm (operatorFrobenius (bilinearSynthesis u X)) := by
  have hnorm : ‖∑ j,exactPrefixBlockWitness u X (lo j) (hi j)‖ ≤ 1 := by
    have hn := (exactCompletedPrefix_norm_energy u lo hi hlo hsep X N).1
    simpa only [exactCompletedPrefix,completedSupportedPrefix,hhi,if_true] using hn
  rw [exact_prefix_diagonal_cross_identity u lo hi hlo X]
  exact inner_operator_le_nuclear (operatorFrobenius (bilinearSynthesis u X)) _ hnorm

theorem exactCompletedPrefix_eq_zero_before {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ) (X : Fin N → Euclid q × Euclid r) {p t : ℕ}
    (hfirst : ∀ j,p ≤ hi j) (ht : t < p) : exactCompletedPrefix u lo hi X t = 0 := by
  unfold exactCompletedPrefix completedSupportedPrefix
  apply Finset.sum_eq_zero
  intro j _
  have hj : ¬ hi j ≤ t := by have := hfirst j; omega
  simp only [hj,if_false]

theorem exactPrefixCross_mask_prefix {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ) (p : ℕ) (hfirst : ∀ j,p ≤ hi j)
    (X : Fin N → Euclid q × Euclid r) :
    exactPrefixCross u (fun i => if i.val < p then 0 else u i) lo hi X =
      exactPrefixCross u u lo hi X := by
  unfold exactPrefixCross
  apply Finset.sum_congr rfl
  intro i _
  by_cases hip : i.val < p
  · rw [exactCompletedPrefix_eq_zero_before u lo hi X hfirst hip]
    simp
  · simp only [hip,if_false]

/-- Exact source assembly for Z0 and the deterministic captured interval. The
sparse-prefix coefficients vanish from the forward cross term. -/
theorem exact_nuclear_lower_from_captured_blocks {n m r s : ℕ}
    (G : ℕ → Finset (Fin n)) (hd : Set.PairwiseDisjoint (↑(Finset.range m) : Set ℕ) G)
    (p q : ℕ) (hpq : p ≤ q) (hqm : q ≤ m) (u : Fin n → ℝ)
    (X : Fin n → Euclid s × Euclid r) :
    (∑ j : CapturedBlockIndex p q,
      spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock u X (capturedBlockLo G p q j) (capturedBlockHi G p q j)))) +
      exactPrefixCross u (fun i => if i.val < supportCut G p then 0 else u i)
        (capturedBlockLo G p q) (capturedBlockHi G p q) X ≤
      spectralNuclearNorm (operatorFrobenius (bilinearSynthesis u X)) := by
  rw [exactPrefixCross_mask_prefix u _ _ _ (capturedBlock_first G p q)]
  exact exact_nuclear_lower_from_prefix_blocks u _ _ (capturedBlock_ordered G p q)
    (capturedBlock_bounded G hd p q hpq hqm) (capturedBlock_separated G p q) X

theorem measurable_exactPrefixCross {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u v : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j) :
    Measurable (exactPrefixCross (r:=r) (q:=q) u v lo hi) := by
  have hm := GaussianEllipsoidCandidate.measurable_gaussianRowSum
    (exactAdaptedPrefix (r:=r) (q:=q) u lo hi)
    (measurable_exactAdaptedPrefix u lo hi) (extendCoefficient v) N
  convert hm using 1
  funext X
  exact exactPrefixCross_eq_rowSum u v lo hi hlo X

theorem exactPrefixCross_rank_weighted_lower_tail {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u v : Fin N → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j,lo j ≤ hi j) (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (V b x : ℝ) (hV : 0 < V) (hb : 0 < b) (hx : 0 ≤ x)
    (hcoef : ∀ i,(v i)^2 ≤ b^2/2)
    (hvar : (∑ i,(v i)^2*(i.val:ℝ)) ≤ V) :
    (gaussianBilinearSampleLaw (Fin N) q r).real {X | exactPrefixCross u v lo hi X ≤ -x} ≤
      Real.exp (-(1/4:ℝ)*min (x^2/V) (x/b)) := by
  have hcap : ∀ k,(extendCoefficient v k)^2 ≤ b^2/2 := by
    intro k
    unfold extendCoefficient
    split_ifs with hk
    · exact hcoef ⟨k,hk⟩
    · nlinarith [sq_nonneg b]
  have hv : (∑ k ∈ Finset.range N,(extendCoefficient v k)^2*(k:ℝ)) ≤ V := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [extendCoefficient,Fin.isLt,dif_pos] using hvar
  have hh := GaussianEllipsoidCandidate.gaussianRowSum_lower_tail
    (exactAdaptedPrefix (r:=r) (q:=q) u lo hi)
    (measurable_exactAdaptedPrefix u lo hi)
    (fun k X => (exactAdaptedPrefix_norm_energy u lo hi hlo hsep k X).1)
    (fun k => (k:ℝ)) (extendCoefficient v)
    (fun k X => (exactAdaptedPrefix_norm_energy u lo hi hlo hsep k X).2)
    N V b x hV hb hx hcap hv
  simpa only [← exactPrefixCross_eq_rowSum u v lo hi hlo] using hh
end GaussianEllipsoid.PaperCanonicalPolar
#print axioms GaussianEllipsoid.PaperCanonicalPolar.exact_prefix_diagonal_cross_identity
#print axioms GaussianEllipsoid.PaperCanonicalPolar.exact_nuclear_lower_from_captured_blocks

#print axioms GaussianEllipsoid.PaperCanonicalPolar.exactPrefixCross_rank_weighted_lower_tail
