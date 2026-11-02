import BilinearPrefixOperators

open MeasureTheory Module
open scoped InnerProductSpace

namespace GaussianEllipsoid

noncomputable def leftIncrement {n r q : ℕ} (X : Fin n → Euclid q × Euclid r) (K L : ℕ) :=
  leftPrefixProjector X L - leftPrefixProjector X K

noncomputable def rightIncrement {n r q : ℕ} (X : Fin n → Euclid q × Euclid r) (K L : ℕ) :=
  rightPrefixProjector X L - rightPrefixProjector X K

noncomputable def projectedPrefixBlock {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) (K L : ℕ) :=
  leftIncrement X K L ∘L prefixBilinearSynthesis u X L ∘L rightIncrement X K L

noncomputable def prefixBlockWitness {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) (K L : ℕ) :=
  supportedMeasurableHalfPolar (projectedPrefixBlock u X K L)
    (leftIncrement X K L) (rightIncrement X K L)

theorem measurable_projectedPrefixBlock {n r q : ℕ} (u : Fin n → ℝ) (K L : ℕ) :
    Measurable (fun X : Fin n → Euclid q × Euclid r => projectedPrefixBlock u X K L) := by
  have hD := (measurable_leftPrefixProjector n r q L).sub (measurable_leftPrefixProjector n r q K)
  have hE := (measurable_rightPrefixProjector n r q L).sub (measurable_rightPrefixProjector n r q K)
  exact (continuous_fst.clm_comp continuous_snd).measurable.comp
    (hD.prodMk ((continuous_fst.clm_comp continuous_snd).measurable.comp
      ((measurable_prefixBilinearSynthesis u L).prodMk hE)))

theorem measurable_prefixBlockWitness {n r q : ℕ} (u : Fin n → ℝ) (K L : ℕ) :
    Measurable (fun X : Fin n → Euclid q × Euclid r => prefixBlockWitness u X K L) :=
  measurable_supported_witness_comp _ _ _ (measurable_projectedPrefixBlock u K L)
    ((measurable_leftPrefixProjector n r q L).sub (measurable_leftPrefixProjector n r q K))
    ((measurable_rightPrefixProjector n r q L).sub (measurable_rightPrefixProjector n r q K))

theorem prefixBlockWitness_properties {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K ≤ L) :
    ‖prefixBlockWitness u X K L‖ ≤ 1 ∧
      leftIncrement X K L ∘L prefixBlockWitness u X K L ∘L rightIncrement X K L =
        prefixBlockWitness u X K L ∧
      spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock u X K L)) / 2 ≤
        ⟪operatorFrobenius (projectedPrefixBlock u X K L),
          operatorFrobenius (prefixBlockWitness u X K L)⟫_ℝ := by
  have hD := prefixSpanProjector_increment_idempotent (fun i => (X i).2) hKL
  have hE := prefixSpanProjector_increment_idempotent (fun i => (X i).1) hKL
  have hT : leftIncrement X K L ∘L projectedPrefixBlock u X K L ∘L rightIncrement X K L =
      projectedPrefixBlock u X K L := by
    apply ContinuousLinearMap.ext
    intro x
    change leftIncrement X K L (leftIncrement X K L
      (prefixBilinearSynthesis u X L (rightIncrement X K L (rightIncrement X K L x)))) = _
    have he := congrArg (fun U : Euclid q →L[ℝ] Euclid q => U x) hE
    change rightIncrement X K L (rightIncrement X K L x) = rightIncrement X K L x at he
    rw [he]
    exact congrArg (fun U : Euclid r →L[ℝ] Euclid r =>
      U (prefixBilinearSynthesis u X L (rightIncrement X K L x))) hD
  have hp := supportedMeasurableHalfPolar_properties (projectedPrefixBlock u X K L)
    (leftIncrement X K L) (rightIncrement X K L)
    (prefixSpanProjector_increment_selfAdjoint _ K L)
    (prefixSpanProjector_increment_selfAdjoint _ K L) hD hE hT
  exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

theorem prefixBlockWitness_local {n r q : ℕ} (u : Fin n → ℝ)
    (X Y : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K ≤ L)
    (hXY : ∀ i, i.val < L → X i = Y i) :
    prefixBlockWitness u X K L = prefixBlockWitness u Y K L := by
  have hLeft (a : ℕ) (ha : a ≤ L) : leftPrefixProjector X a = leftPrefixProjector Y a :=
    prefixSpanProjector_local _ _ a (fun i hi => congrArg Prod.snd (hXY i (hi.trans_le ha)))
  have hRight (a : ℕ) (ha : a ≤ L) : rightPrefixProjector X a = rightPrefixProjector Y a :=
    prefixSpanProjector_local _ _ a (fun i hi => congrArg Prod.fst (hXY i (hi.trans_le ha)))
  simp only [prefixBlockWitness, projectedPrefixBlock, leftIncrement, rightIncrement,
    hLeft K hKL, hLeft L (le_refl L), hRight K hKL, hRight L (le_refl L),
    prefixBilinearSynthesis_local u X Y L hXY]

theorem prefix_increments_orthogonal {n q : ℕ} (f : Fin n → Euclid q)
    {K L M N : ℕ} (hKL : K ≤ L) (hMN : M ≤ N) (hsep : L ≤ M ∨ N ≤ K) :
    (prefixSpanProjector f L - prefixSpanProjector f K) ∘L
      (prefixSpanProjector f N - prefixSpanProjector f M) = 0 := by
  rcases hsep with h | h
  · exact prefixSpanProjector_increments_comp_zero f hKL h hMN
  · have hc := congrArg ContinuousLinearMap.adjoint
      (prefixSpanProjector_increments_comp_zero f hMN h hKL)
    simpa only [ContinuousLinearMap.adjoint_comp, map_sub,
      prefixSpanProjector_selfAdjoint, map_zero] using hc

noncomputable def completedPrefixWitness {ι : Type*} [Fintype ι]
    {n r q : ℕ} (u : Fin n → ℝ) (lo hi : ι → ℕ)
    (X : Fin n → Euclid q × Euclid r) (t : ℕ) :=
  ∑ j, if hi j ≤ t then prefixBlockWitness u X (lo j) (hi j) else 0

theorem measurable_completedPrefixWitness {ι : Type*} [Fintype ι]
    {n r q : ℕ} (u : Fin n → ℝ) (lo hi : ι → ℕ) (t : ℕ) :
    Measurable (fun X : Fin n → Euclid q × Euclid r => completedPrefixWitness u lo hi X t) := by
  apply Finset.measurable_sum
  intro j _
  by_cases hj : hi j ≤ t
  · simpa only [hj, if_true] using measurable_prefixBlockWitness (r := r) (q := q) u (lo j) (hi j)
  · simp only [hj, if_false]; exact measurable_const

theorem norm_completedPrefixWitness_le_one {ι : Type*} [Fintype ι]
    {n r q : ℕ} (u : Fin n → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j, lo j ≤ hi j) (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (X : Fin n → Euclid q × Euclid r) (t : ℕ) :
    ‖completedPrefixWitness u lo hi X t‖ ≤ 1 := by
  apply norm_sum_supported_le_one (fun j => leftIncrement X (lo j) (hi j))
    (fun j => rightIncrement X (lo j) (hi j)) _
  · intro j; exact prefixSpanProjector_increment_selfAdjoint _ _ _
  · intro j; exact prefixSpanProjector_increment_selfAdjoint _ _ _
  · intro j; exact prefixSpanProjector_increment_idempotent _ (hlo j)
  · intro j; exact prefixSpanProjector_increment_idempotent _ (hlo j)
  · intro i j hij; exact prefix_increments_orthogonal _ (hlo i) (hlo j) (hsep i j hij)
  · intro i j hij; exact prefix_increments_orthogonal _ (hlo i) (hlo j) (hsep i j hij)
  · intro j; split_ifs
    · exact (prefixBlockWitness_properties u X (hlo j)).1
    · simp
  · intro j; split_ifs
    · exact (prefixBlockWitness_properties u X (hlo j)).2.1
    · simp

theorem completedPrefixWitness_local {ι : Type*} [Fintype ι]
    {n r q : ℕ} (u : Fin n → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (X Y : Fin n → Euclid q × Euclid r) (t : ℕ)
    (hXY : ∀ i, i.val < t → X i = Y i) :
    completedPrefixWitness u lo hi X t = completedPrefixWitness u lo hi Y t := by
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · exact prefixBlockWitness_local u X Y (hlo j) (fun i hi => hXY i (hi.trans_le hj))
  · rfl

#print axioms measurable_projectedPrefixBlock
#print axioms measurable_prefixBlockWitness
#print axioms prefixBlockWitness_properties
#print axioms prefixBlockWitness_local
#print axioms prefix_increments_orthogonal
#print axioms measurable_completedPrefixWitness
#print axioms norm_completedPrefixWitness_le_one
#print axioms completedPrefixWitness_local
end GaussianEllipsoid
