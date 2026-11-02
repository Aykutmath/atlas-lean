import PaperCanonicalPolarFull
import PrefixBlockInterfaces
import AdaptedPrefixWitness
import BMSpectralPositive
import SupportedPrefixAggregate

noncomputable section
open MeasureTheory Module
open scoped InnerProductSpace BigOperators
namespace GaussianEllipsoid.PaperCanonicalPolar

def exactPrefixBlockWitness {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) (K L : ℕ) : Euclid q →L[ℝ] Euclid r :=
  polarWitness (projectedPrefixBlock u X K L)

/-- The literal canonical partial-polar block witness is Borel in the revealed samples. -/
theorem measurable_exactPrefixBlockWitness {n r q : ℕ} (u : Fin n → ℝ) (K L : ℕ) :
    Measurable (fun X : Fin n → Euclid q × Euclid r => exactPrefixBlockWitness u X K L) :=
  (polarWitness_measurable r q).comp (measurable_projectedPrefixBlock u K L)

/-- Exact nuclear attainment, rather than a constant-fraction substitute. -/
theorem exactPrefixBlockWitness_properties {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K≤L) :
    ‖exactPrefixBlockWitness u X K L‖≤1 ∧
      leftIncrement X K L ∘L exactPrefixBlockWitness u X K L ∘L rightIncrement X K L=
        exactPrefixBlockWitness u X K L ∧
      ⟪operatorFrobenius (projectedPrefixBlock u X K L),
        operatorFrobenius (exactPrefixBlockWitness u X K L)⟫_ℝ=
        spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock u X K L)) ∧
      ‖operatorFrobenius (exactPrefixBlockWitness u X K L)‖^2≤
        (finrank ℝ (LinearMap.range (rightIncrement X K L).toLinearMap):ℝ) := by
  have hD := prefixSpanProjector_increment_idempotent (fun i => (X i).2) hKL
  have hE := prefixSpanProjector_increment_idempotent (fun i => (X i).1) hKL
  have hT : leftIncrement X K L ∘L projectedPrefixBlock u X K L ∘L rightIncrement X K L=
      projectedPrefixBlock u X K L := by
    apply ContinuousLinearMap.ext
    intro x
    change leftIncrement X K L (leftIncrement X K L
      (prefixBilinearSynthesis u X L (rightIncrement X K L (rightIncrement X K L x))))=_
    have he := congrArg (fun U : Euclid q →L[ℝ] Euclid q => U x) hE
    change rightIncrement X K L (rightIncrement X K L x)=rightIncrement X K L x at he
    rw [he]
    exact congrArg (fun U : Euclid r →L[ℝ] Euclid r =>
      U (prefixBilinearSynthesis u X L (rightIncrement X K L x))) hD
  exact canonical_supported_polar (projectedPrefixBlock u X K L)
    (leftIncrement X K L) (rightIncrement X K L)
    (prefixSpanProjector_increment_selfAdjoint _ K L)
    (prefixSpanProjector_increment_selfAdjoint _ K L) hD hE hT

theorem exactPrefixBlockWitness_local {n r q : ℕ} (u : Fin n → ℝ)
    (X Y : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K≤L)
    (hXY : ∀ i,i.val<L → X i=Y i) :
    exactPrefixBlockWitness u X K L=exactPrefixBlockWitness u Y K L := by
  have hLeft (a : ℕ) (ha : a≤L) : leftPrefixProjector X a=leftPrefixProjector Y a :=
    prefixSpanProjector_local _ _ a (fun i hi => congrArg Prod.snd (hXY i (hi.trans_le ha)))
  have hRight (a : ℕ) (ha : a≤L) : rightPrefixProjector X a=rightPrefixProjector Y a :=
    prefixSpanProjector_local _ _ a (fun i hi => congrArg Prod.fst (hXY i (hi.trans_le ha)))
  simp only [exactPrefixBlockWitness,projectedPrefixBlock,leftIncrement,rightIncrement,
    hLeft K hKL,hLeft L le_rfl,hRight K hKL,hRight L le_rfl,
    prefixBilinearSynthesis_local u X Y L hXY]

/-- Exact source residual-block formula, including the removed preceding spans. -/
theorem exactPrefixBlockWitness_residual {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K≤L) :
    exactPrefixBlockWitness u X K L = canonicalOperator
      ((ContinuousLinearMap.id ℝ (Euclid r)-leftPrefixProjector X K) ∘L
        bilinearSynthesis (fun i => if K ≤ i.val ∧ i.val < L then u i else 0) X ∘L
        (ContinuousLinearMap.id ℝ (Euclid q)-rightPrefixProjector X K)) := by
  rw [canonicalOperator_eq_polarWitness,← projectedPrefixBlock_eq_residual u X hKL]
  rfl

/-- Every backward prefix pairing vanishes pathwise for the same exact canonical witness. -/
theorem exactPrefixBlockWitness_earlier {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {J K L : ℕ} (hJK : J≤K) (hKL : K≤L) :
    ⟪operatorFrobenius (prefixBilinearSynthesis u X J),
      operatorFrobenius (exactPrefixBlockWitness u X K L)⟫_ℝ=0 := by
  have hd : leftIncrement X K L ∘L prefixBilinearSynthesis u X J=0 := by
    unfold leftIncrement
    rw [ContinuousLinearMap.sub_comp,leftPrefixProjector_synthesis u X (hJK.trans hKL),
      leftPrefixProjector_synthesis u X hJK,sub_self]
  apply inner_supported_eq_zero_of_compression_zero (leftIncrement X K L) (rightIncrement X K L)
    _ _ (prefixSpanProjector_increment_selfAdjoint _ K L)
    (prefixSpanProjector_increment_selfAdjoint _ K L)
    (exactPrefixBlockWitness_properties u X hKL).2.1
  rw [← ContinuousLinearMap.comp_assoc,hd,ContinuousLinearMap.zero_comp]

def exactCompletedPrefix {ι : Type*} [Fintype ι] {n r q : ℕ}
    (u : Fin n → ℝ) (lo hi : ι → ℕ) (X : Fin n → Euclid q × Euclid r) (t : ℕ) :
    Euclid q →L[ℝ] Euclid r :=
  completedSupportedPrefix (fun j => exactPrefixBlockWitness u X (lo j) (hi j)) hi t

theorem measurable_exactCompletedPrefix {ι : Type*} [Fintype ι] {n r q : ℕ}
    (u : Fin n → ℝ) (lo hi : ι → ℕ) (t : ℕ) :
    Measurable (fun X : Fin n → Euclid q × Euclid r => exactCompletedPrefix u lo hi X t) :=
  measurable_completedSupportedPrefix _
    (fun j => measurable_exactPrefixBlockWitness u (lo j) (hi j)) hi t

lemma contraction_gram_le_identity {r q : ℕ} (W : Euclid q →L[ℝ] Euclid r)
    (hW : ‖W‖≤1) : BMGeometry.IsPSD (ContinuousLinearMap.id ℝ (Euclid q)-W.adjoint ∘L W) := by
  constructor
  · intro x y
    change ⟪x-W.adjoint (W x),y⟫_ℝ=⟪x,y-W.adjoint (W y)⟫_ℝ
    rw [inner_sub_left,inner_sub_right,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
  · intro x
    change 0≤⟪x-W.adjoint (W x),x⟫_ℝ
    rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]
    have hn : ‖W x‖ ≤ ‖x‖ := (W.le_opNorm x).trans (by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hW (norm_nonneg x)))
    nlinarith [norm_nonneg (W x),norm_nonneg x]

/-- Completed source-canonical witnesses have the same exact contraction and
rank energy properties as the general supported aggregate. -/
theorem exactCompletedPrefix_norm_energy {ι : Type*} [Fintype ι] {n r q : ℕ}
    (u : Fin n → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j,lo j≤hi j) (hsep : ∀ i j,i≠j → hi i≤lo j ∨ hi j≤lo i)
    (X : Fin n → Euclid q × Euclid r) (t : ℕ) :
    ‖exactCompletedPrefix u lo hi X t‖≤1 ∧
      exactCompletedPrefix u lo hi X t ∘L rightPrefixProjector X t=exactCompletedPrefix u lo hi X t ∧
      ‖operatorFrobenius (exactCompletedPrefix u lo hi X t)‖^2≤(t:ℝ) := by
  have hn j := (exactPrefixBlockWitness_properties u X (hlo j)).1
  have hs j := (exactPrefixBlockWitness_properties u X (hlo j)).2.1
  exact ⟨completedSupportedPrefix_norm_le_one X _ lo hi hlo hsep hn hs t,
    completedSupportedPrefix_right_prefix X _ lo hi hlo hs t,
    completedSupportedPrefix_energy_le_prefix_length X _ lo hi hlo hsep hn hs t⟩

theorem exactCompletedPrefix_gram_le_identity {ι : Type*} [Fintype ι] {n r q : ℕ}
    (u : Fin n → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j,lo j≤hi j) (hsep : ∀ i j,i≠j → hi i≤lo j ∨ hi j≤lo i)
    (X : Fin n → Euclid q × Euclid r) (t : ℕ) :
    BMGeometry.IsPSD (ContinuousLinearMap.id ℝ (Euclid q)-
      (exactCompletedPrefix u lo hi X t).adjoint ∘L exactCompletedPrefix u lo hi X t) :=
  contraction_gram_le_identity _ (exactCompletedPrefix_norm_energy u lo hi hlo hsep X t).1

theorem exactCompletedPrefix_local {ι : Type*} [Fintype ι] {n r q : ℕ}
    (u : Fin n → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j≤hi j)
    (X Y : Fin n → Euclid q × Euclid r) (t : ℕ)
    (hXY : ∀ i,i.val<t → X i=Y i) :
    exactCompletedPrefix u lo hi X t=exactCompletedPrefix u lo hi Y t := by
  unfold exactCompletedPrefix completedSupportedPrefix
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : hi j≤t
  · simp only [if_pos hj]
    exact exactPrefixBlockWitness_local u X Y (hlo j)
      (fun i hi => hXY i (hi.trans_le hj))
  · simp only [if_neg hj]

def exactAdaptedPrefix {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ) (k : ℕ) (X : Fin k → Euclid q × Euclid r) :
    Euclid q →L[ℝ] Euclid r := exactCompletedPrefix u lo hi (zeroExtendRows N X) k

theorem measurable_exactAdaptedPrefix {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ) (k : ℕ) :
    Measurable (exactAdaptedPrefix (r := r) (q := q) u lo hi k) :=
  (measurable_exactCompletedPrefix u lo hi k).comp (measurable_zeroExtendRows N k r q)

theorem exactAdaptedPrefix_norm_energy {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j,lo j≤hi j) (hsep : ∀ i j,i≠j → hi i≤lo j ∨ hi j≤lo i)
    (k : ℕ) (X : Fin k → Euclid q × Euclid r) :
    ‖exactAdaptedPrefix u lo hi k X‖≤1 ∧
      ‖operatorFrobenius (exactAdaptedPrefix u lo hi k X)‖^2≤(k:ℝ) :=
  ⟨(exactCompletedPrefix_norm_energy u lo hi hlo hsep _ _).1,
    (exactCompletedPrefix_norm_energy u lo hi hlo hsep _ _).2.2⟩

theorem exactAdaptedPrefix_on_history {ι : Type*} [Fintype ι] {N r q : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j,lo j≤hi j)
    (X : Fin N → Euclid q × Euclid r) (i : Fin N) :
    exactAdaptedPrefix u lo hi i.val (fun j : Fin i.val => X ⟨j.val,j.isLt.trans i.isLt⟩)=
      exactCompletedPrefix u lo hi X i.val := by
  apply exactCompletedPrefix_local u lo hi hlo _ _ _
  intro j hj
  simp only [zeroExtendRows,hj,dif_pos]

#print axioms measurable_exactAdaptedPrefix
#print axioms exactAdaptedPrefix_norm_energy
#print axioms exactCompletedPrefix_norm_energy
#print axioms measurable_exactCompletedPrefix
#print axioms measurable_exactPrefixBlockWitness
#print axioms exactPrefixBlockWitness_properties
end GaussianEllipsoid.PaperCanonicalPolar
