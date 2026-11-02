import SpectralFrobenius
import SingularTail

noncomputable section
open Set Metric Module
open scoped BigOperators
namespace GaussianEllipsoid

@[simp] theorem operatorFrobenius_sub {r q : ℕ}
    (S T : Euclid q →L[ℝ] Euclid r) :
    operatorFrobenius (S - T) = operatorFrobenius S - operatorFrobenius T := by
  ext j i; rfl

theorem basisBlock_sub_of_subset {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) {I J : Finset (Fin q)} (hIJ : I ⊆ J) :
    basisBlock T b J - basisBlock T b I = basisBlock T b (J \ I) := by
  classical
  dsimp [basisBlock]
  exact (eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hIJ)).symm

/-- A genuine spectral rank block of a matrix. -/
def spectralPiece {r q : ℕ} (A : FrobeniusMatrix r q) (I : Finset (Fin q)) : FrobeniusMatrix r q :=
  operatorFrobenius (basisBlock (frobeniusOperator A)
    (orderedSingularBasis (frobeniusOperator A)) I)

@[simp] theorem spectralPiece_univ {r q : ℕ} (A : FrobeniusMatrix r q) :
    spectralPiece A Finset.univ = A := by
  simp only [spectralPiece, basisBlock_univ, operatorFrobenius_frobeniusOperator]

theorem spectralPiece_sub_of_subset {r q : ℕ} (A : FrobeniusMatrix r q)
    {I J : Finset (Fin q)} (hIJ : I ⊆ J) :
    spectralPiece A J - spectralPiece A I = spectralPiece A (J \ I) := by
  simp only [spectralPiece, ← operatorFrobenius_sub, basisBlock_sub_of_subset _ _ hIJ]

theorem norm_spectralPiece_sq {r q : ℕ} (A : FrobeniusMatrix r q) (I : Finset (Fin q)) :
    ‖spectralPiece A I‖ ^ 2 = ∑ i ∈ I, (orderedSingularValue (frobeniusOperator A) i) ^ 2 := by
  simp only [spectralPiece, norm_basisBlock_sq, norm_orderedSingularBasis]

theorem rank_spectralPiece_le {r q : ℕ} (A : FrobeniusMatrix r q) (I : Finset (Fin q)) :
    (frobeniusToMatrix (spectralPiece A I)).rank ≤ I.card := rank_basisBlock_le _ _ _

/-- Frobenius tail estimate derived from the actual ordered Gram spectrum. -/
theorem norm_spectralPiece_sq_le {r q : ℕ} (A : FrobeniusMatrix r q)
    {R : ℝ} (hR : 0 ≤ R) (hA : spectralNuclearNorm A ≤ R)
    (I : Finset (Fin q)) {K : ℕ} (hK : 0 < K)
    (hI : ∀ i ∈ I, K ≤ i.val + 1) :
    ‖spectralPiece A I‖ ^ 2 ≤ R ^ 2 / K := by
  rw [norm_spectralPiece_sq]
  exact antitone_sum_sq_tail_le _ (orderedSingularValue_nonneg _) (orderedSingularValue_antitone _)
    hR ((sum_orderedSingularValue A).trans_le hA) I hK hI

def prefixIndices (q K : ℕ) : Finset (Fin q) := Finset.univ.filter (fun i => i.val < K)

@[simp] theorem mem_prefixIndices {q K : ℕ} {i : Fin q} :
    i ∈ prefixIndices q K ↔ i.val < K := by simp [prefixIndices]

theorem prefixIndices_mono {q K L : ℕ} (hKL : K ≤ L) : prefixIndices q K ⊆ prefixIndices q L := by
  intro i hi; exact mem_prefixIndices.mpr ((mem_prefixIndices.mp hi).trans_le hKL)

theorem card_prefixIndices_le (q K : ℕ) : (prefixIndices q K).card ≤ K := by
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn (t := Finset.range K)
    Fin.val (fun i hi => Finset.mem_range.mpr (mem_prefixIndices.mp hi))
    (fun i _ j _ h => Fin.ext h)

def spectralPrefix {r q : ℕ} (A : FrobeniusMatrix r q) (K : ℕ) := spectralPiece A (prefixIndices q K)

theorem norm_spectralTail_sq_le {r q K : ℕ} (A : FrobeniusMatrix r q)
    {R : ℝ} (hR : 0 ≤ R) (hA : spectralNuclearNorm A ≤ R) (hK : 0 < K) :
    ‖A - spectralPrefix A K‖ ^ 2 ≤ R ^ 2 / K := by
  have heq : A - spectralPrefix A K = spectralPiece A (Finset.univ \ prefixIndices q K) := by
    simpa only [spectralPiece_univ, spectralPrefix] using
      spectralPiece_sub_of_subset A (Finset.subset_univ (prefixIndices q K))
  rw [heq]
  apply norm_spectralPiece_sq_le A hR hA _ hK
  intro i hi
  have := Finset.mem_sdiff.mp hi
  have : K ≤ i.val := by simpa only [mem_prefixIndices, not_lt] using this.2
  omega

/-- Four-adic spectral blocks avoid square-root powers in the covering argument. -/
def fourAdicBlock {r q : ℕ} (A : FrobeniusMatrix r q) : ℕ → FrobeniusMatrix r q
  | 0 => spectralPrefix A 1
  | j + 1 => spectralPrefix A (4 ^ (j + 1)) - spectralPrefix A (4 ^ j)

theorem sum_fourAdicBlock {r q : ℕ} (A : FrobeniusMatrix r q) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), fourAdicBlock A j = spectralPrefix A (4 ^ J) := by
  induction J with
  | zero => simp [fourAdicBlock]
  | succ J hJ =>
    rw [Finset.sum_range_succ, hJ]
    simp only [fourAdicBlock]
    abel

theorem fourAdicBlock_succ_eq {r q : ℕ} (A : FrobeniusMatrix r q) (j : ℕ) :
    fourAdicBlock A (j + 1) = spectralPiece A
      (prefixIndices q (4 ^ (j + 1)) \ prefixIndices q (4 ^ j)) := by
  apply spectralPiece_sub_of_subset
  exact prefixIndices_mono (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j))

theorem rank_fourAdicBlock_le {r q : ℕ} (A : FrobeniusMatrix r q) (j : ℕ) :
    (frobeniusToMatrix (fourAdicBlock A j)).rank ≤ 4 ^ j := by
  cases j with
  | zero => exact (rank_spectralPiece_le A _).trans (card_prefixIndices_le q 1)
  | succ j =>
    rw [fourAdicBlock_succ_eq]
    exact (rank_spectralPiece_le A _).trans
      ((Finset.card_le_card Finset.sdiff_subset).trans (card_prefixIndices_le q _))

/-- The four-adic block radius is derived from the mass-times-threshold tail
bound, with constant 2 and no square-root rank loss. -/
theorem norm_fourAdicBlock_le {r q : ℕ} (A : FrobeniusMatrix r q)
    {R : ℝ} (hR : 0 ≤ R) (hA : spectralNuclearNorm A ≤ R) (j : ℕ) :
    ‖fourAdicBlock A j‖ ≤ 2 * R / (2 : ℝ) ^ j := by
  have hpow (j : ℕ) : ((4 ^ j : ℕ) : ℝ) = ((2 : ℝ) ^ j) ^ 2 := by
    push_cast
    rw [← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  cases j with
  | zero =>
    have hb := norm_spectralPiece_sq_le A hR hA (prefixIndices q 1)
      (K := 1) (by omega) (by intro i hi; omega)
    change ‖fourAdicBlock A 0‖ ^ 2 ≤ R ^ 2 / (1 : ℕ) at hb
    norm_num only [Nat.cast_one, div_one] at hb
    have hn := norm_nonneg (fourAdicBlock A 0)
    simp only [pow_zero, div_one]
    nlinarith
  | succ j =>
    rw [fourAdicBlock_succ_eq]
    have hb := norm_spectralPiece_sq_le A hR hA
      (prefixIndices q (4 ^ (j + 1)) \ prefixIndices q (4 ^ j))
      (K := 4 ^ j) (by positivity) (by
        intro i hi
        have := (Finset.mem_sdiff.mp hi).2
        have : 4 ^ j ≤ i.val := by simpa only [mem_prefixIndices, not_lt] using this
        omega)
    have hRad : (2 * R / (2 : ℝ) ^ (j + 1)) ^ 2 = R ^ 2 / (4 ^ j : ℕ) := by
      rw [hpow, pow_succ]
      field_simp
      <;> ring
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rwa [hRad]

end GaussianEllipsoid
#print axioms GaussianEllipsoid.norm_spectralTail_sq_le
#print axioms GaussianEllipsoid.sum_fourAdicBlock
#print axioms GaussianEllipsoid.rank_fourAdicBlock_le
#print axioms GaussianEllipsoid.norm_fourAdicBlock_le
