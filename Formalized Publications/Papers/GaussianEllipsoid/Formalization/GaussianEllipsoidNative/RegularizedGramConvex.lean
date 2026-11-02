import CappedPairwise
import RankTwoDeterminant

noncomputable section
open Finset Matrix Set

namespace GaussianEllipsoid.CappedSimplex

local instance : StarOrderedRing ℝ := RCLike.toStarOrderedRing

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The coefficient constraints form a convex slice. -/
theorem convex_slice (a b : ℝ) : Convex ℝ (slice (ι := κ) a b) := by
  intro w hw v hv p q hp hq hpq
  constructor
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · exact add_nonneg (mul_nonneg hp (hw.1 i).1) (mul_nonneg hq (hv.1 i).1)
    · calc p * w i + q * v i ≤ p * a + q * a :=
            add_le_add (mul_le_mul_of_nonneg_left (hw.1 i).2 hp)
              (mul_le_mul_of_nonneg_left (hv.1 i).2 hq)
          _ = a := by rw [← add_mul, hpq, one_mul]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hw.2, hv.2]
    rw [← add_mul, hpq, one_mul]

/-- Taking a line of coefficient transfers preserves convexity of its domain. -/
theorem convex_transfer_domain (a b : ℝ) (w : κ → ℝ) (i j : κ) :
    Convex ℝ {t : ℝ | transfer w i j t ∈ slice a b} := by
  intro x hx y hy p q hp hq hpq
  have h := convex_slice a b hx hy hp hq hpq
  have heq : transfer w i j (p * x + q * y) =
      p • transfer w i j x + q • transfer w i j y := by
    funext k
    simp only [transfer, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hprod := congrArg (fun z : ℝ => z * w k) hpq
    split_ifs <;> nlinarith [hprod]
  change transfer w i j (p * x + q * y) ∈ slice a b
  rw [heq]
  exact h

/-- Weighted rank-one covariance, without probabilistic assumptions. -/
def weightedGram (g : κ → ι → ℝ) (w : κ → ℝ) : Matrix ι ι ℝ :=
  ∑ k, w k • Matrix.vecMulVec (g k) (g k)

def regularizedGram (ε : ℝ) (g : κ → ι → ℝ) (w : κ → ℝ) : Matrix ι ι ℝ :=
  ε • 1 + weightedGram g w

/-- Nonnegative covariance weights give a positive-semidefinite Gram matrix. -/
theorem weightedGram_posSemidef (g : κ → ι → ℝ) {w : κ → ℝ}
    (hw : ∀ k, 0 ≤ w k) : (weightedGram g w).PosSemidef := by
  let G : Matrix ι κ ℝ := fun i k => g k i
  have hdiag : (Matrix.diagonal w).PosSemidef := Matrix.PosSemidef.diagonal hw
  have hgram := hdiag.mul_mul_conjTranspose_same G
  have heq : weightedGram g w = G * Matrix.diagonal w * G.transpose := by
    ext i j
    change (weightedGram g w) i j = ∑ k, (G * Matrix.diagonal w) i k * G.transpose k j
    simp only [weightedGram, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.vecMulVec, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    dsimp only [G]
    ring
  rw [heq]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hgram

/-- A positive ridge makes every nonnegative weighted covariance positive definite. -/
theorem regularizedGram_posDef {ε : ℝ} (hε : 0 < ε) (g : κ → ι → ℝ)
    {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) : (regularizedGram ε g w).PosDef := by
  have hI : (ε • (1 : Matrix ι ι ℝ)).PosDef := by
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.PosDef.diagonal (fun _ => hε)
  exact hI.add_posSemidef (weightedGram_posSemidef g hw)

/-- Transferring two weights is precisely a signed rank-two matrix update. -/
theorem weightedGram_transfer (g : κ → ι → ℝ) (w : κ → ℝ) (i j : κ) (t : ℝ) :
    weightedGram g (transfer w i j t) =
      weightedGram g w + t • (Matrix.vecMulVec (g i) (g i) - Matrix.vecMulVec (g j) (g j)) := by
  ext p q
  simp [weightedGram, transfer, Matrix.vecMulVec, Matrix.sum_apply,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    smul_eq_mul, ite_mul]
  ring

theorem regularizedGram_transfer (ε : ℝ) (g : κ → ι → ℝ) (w : κ → ℝ)
    (i j : κ) (t : ℝ) :
    regularizedGram ε g (transfer w i j t) =
      regularizedGram ε g w +
        t • (Matrix.vecMulVec (g i) (g i) - Matrix.vecMulVec (g j) (g j)) := by
  simp only [regularizedGram, weightedGram_transfer]
  abel

/-- The inverse determinant moment integrand satisfies exactly the pairwise
convexity needed by capped rounding. No log-determinant theorem is used. -/
theorem pairwiseConvex_regularized_det_neg_nat_zpow {ε : ℝ} (hε : 0 < ε)
    (g : κ → ι → ℝ) (a b : ℝ) (s : ℕ) :
    PairwiseConvex a b (fun w => (Matrix.det (regularizedGram ε g w)) ^ (-(s : ℤ))) := by
  intro w hw i j _
  have hA : (regularizedGram ε g w).PosDef :=
    regularizedGram_posDef hε g (fun k => (hw.1 k).1)
  simp only [regularizedGram_transfer]
  apply convexOn_det_rankTwo_neg_nat_zpow hA (g i) (g j)
    (convex_transfer_domain a b w i j)
  intro t ht
  rw [← regularizedGram_transfer]
  exact regularizedGram_posDef hε g (fun k => (ht.1 k).1)

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.pairwiseConvex_regularized_det_neg_nat_zpow
