import BilinearGroupWitness
import GaussianRowMartingale

open MeasureTheory GaussianEllipsoidCandidate
open scoped InnerProductSpace

namespace GaussianEllipsoid

/-- An operator contraction has Frobenius energy at most its domain dimension. -/
theorem frobenius_contraction_energy {r q : ℕ} (W : Euclid q →L[ℝ] Euclid r) (hW : ‖W‖ ≤ 1) :
    ‖operatorFrobenius W‖^2 ≤ (q : ℝ) := by
  rw [← sum_norm_sq_operator_basis W (EuclideanSpace.basisFun (Fin q) ℝ)]
  calc
    ∑ i, ‖W (EuclideanSpace.basisFun (Fin q) ℝ i)‖^2 ≤ ∑ _i : Fin q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := W.le_opNorm (EuclideanSpace.basisFun (Fin q) ℝ i)
      rw [(EuclideanSpace.basisFun (Fin q) ℝ).norm_eq_one, mul_one] at h
      have hn := h.trans hW
      simpa using pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = q := by simp

/-- Pad the unrevealed coordinates by zero while retaining the fixed master
index type. No randomness beyond the revealed prefix enters this map. -/
def zeroExtendRows {k r q : ℕ} (N : ℕ) (X : Fin k → Euclid q × Euclid r) :
    Fin N → Euclid q × Euclid r := fun i => if h : i.val < k then X ⟨i.val,h⟩ else 0

theorem measurable_zeroExtendRows (N k r q : ℕ) :
    Measurable (zeroExtendRows (r := r) (q := q) (k := k) N) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i.val < k
  · simpa only [zeroExtendRows, h, dif_pos] using
      (measurable_pi_apply (⟨i.val,h⟩ : Fin k) :
        Measurable (fun X : Fin k → Euclid q × Euclid r => X ⟨i.val,h⟩))
  · simp only [zeroExtendRows, h, dif_neg]; exact measurable_const

noncomputable def adaptedPrefixWitness {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u : Fin N → ℝ) (lo hi : ι → ℕ) (k : ℕ)
    (X : Fin k → Euclid q × Euclid r) :=
  completedPrefixWitness u lo hi (zeroExtendRows N X) k

theorem measurable_adaptedPrefixWitness {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u : Fin N → ℝ) (lo hi : ι → ℕ) (k : ℕ) :
    Measurable (adaptedPrefixWitness (r := r) (q := q) u lo hi k) :=
  (measurable_completedPrefixWitness u lo hi k).comp (measurable_zeroExtendRows N k r q)

theorem norm_adaptedPrefixWitness_le_one {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u : Fin N → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j, lo j ≤ hi j) (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (k : ℕ) (X : Fin k → Euclid q × Euclid r) :
    ‖adaptedPrefixWitness u lo hi k X‖ ≤ 1 :=
  norm_completedPrefixWitness_le_one u lo hi hlo hsep _ _

theorem adaptedPrefixWitness_on_history {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (X : Fin N → Euclid q × Euclid r) (i : Fin N) :
    adaptedPrefixWitness u lo hi i.val
        (fun j : Fin i.val => X ⟨j.val, j.isLt.trans i.isLt⟩) =
      completedPrefixWitness u lo hi X i.val := by
  apply completedPrefixWitness_local u lo hi hlo _ _ _
  intro j hj
  simp only [zeroExtendRows, hj, dif_pos]

/-- Explicit finite-sum form of the already-verified adapted row process. -/
theorem gaussianRowSum_eq_fin_sum {r q : ℕ}
    (W : ∀ k : ℕ, (Fin k → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (u : ℕ → ℝ) (n : ℕ) (X : Fin n → Euclid q × Euclid r) :
    gaussianRowSum W u n X = ∑ i : Fin n, u i.val *
      ⟪W i.val (fun j : Fin i.val => X ⟨j.val, j.isLt.trans i.isLt⟩) (X i).1, (X i).2⟫_ℝ := by
  induction n with
  | zero => simp [gaussianRowSum]
  | succ n ih =>
    rw [gaussianRowSum, Fin.sum_univ_castSucc, ih]
    rfl

noncomputable def prefixWitnessCross {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u v : Fin N → ℝ) (lo hi : ι → ℕ)
    (X : Fin N → Euclid q × Euclid r) : ℝ :=
  ∑ i, v i * ⟪completedPrefixWitness u lo hi X i.val (X i).1,(X i).2⟫_ℝ

def extendCoefficient {N : ℕ} (v : Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k < N then v ⟨k,h⟩ else 0

theorem prefixWitnessCross_eq_rowSum {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u v : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (X : Fin N → Euclid q × Euclid r) :
    prefixWitnessCross u v lo hi X =
      gaussianRowSum (adaptedPrefixWitness u lo hi) (extendCoefficient v) N X := by
  rw [gaussianRowSum_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [adaptedPrefixWitness_on_history u lo hi hlo]
  simp only [extendCoefficient, i.isLt, dif_pos]

theorem measurable_prefixWitnessCross {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u v : Fin N → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j) :
    Measurable (prefixWitnessCross (r := r) (q := q) u v lo hi) := by
  have h := measurable_gaussianRowSum (adaptedPrefixWitness (r := r) (q := q) u lo hi)
    (measurable_adaptedPrefixWitness u lo hi) (extendCoefficient v) N
  convert h using 1
  funext X
  exact prefixWitnessCross_eq_rowSum u v lo hi hlo X

/-- The actual cross-term tail for constructed prefix witnesses. All adapted
operators, measurability, contractions and Gaussian MGFs are proved internally.
Only deterministic interval separation and scalar coefficient bounds remain. -/
theorem prefixWitnessCross_lower_tail {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u v : Fin N → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j, lo j ≤ hi j) (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (V b x : ℝ) (hV : 0 < V) (hb : 0 < b) (hx : 0 ≤ x)
    (hcoef : ∀ i, (v i)^2 ≤ b^2/2) (hvar : (q : ℝ) * ∑ i, (v i)^2 ≤ V) :
    (gaussianBilinearSampleLaw (Fin N) q r).real {X | prefixWitnessCross u v lo hi X ≤ -x} ≤
      Real.exp (-(1/4 : ℝ) * min (x^2/V) (x/b)) := by
  have hcap : ∀ k, (extendCoefficient v k)^2 ≤ b^2/2 := by
    intro k
    unfold extendCoefficient
    split_ifs with hk
    · exact hcoef ⟨k,hk⟩
    · nlinarith [sq_nonneg b]
  have hv : (∑ k ∈ Finset.range N, (extendCoefficient v k)^2 * (q : ℝ)) ≤ V := by
    rw [← Fin.sum_univ_eq_sum_range]
    have heq : (∑ i : Fin N, (extendCoefficient v i.val)^2 * (q : ℝ)) =
        (q : ℝ) * ∑ i, (v i)^2 := by
      simp only [extendCoefficient, Fin.isLt, dif_pos]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    exact heq ▸ hvar
  have h := gaussianRowSum_lower_tail (adaptedPrefixWitness (r := r) (q := q) u lo hi)
    (measurable_adaptedPrefixWitness u lo hi)
    (norm_adaptedPrefixWitness_le_one u lo hi hlo hsep) (fun _ => (q : ℝ))
    (extendCoefficient v) (fun k X => frobenius_contraction_energy _
      (norm_adaptedPrefixWitness_le_one u lo hi hlo hsep k X)) N V b x hV hb hx hcap hv
  simpa only [← prefixWitnessCross_eq_rowSum u v lo hi hlo] using h

#print axioms frobenius_contraction_energy
#print axioms measurable_zeroExtendRows
#print axioms measurable_adaptedPrefixWitness
#print axioms norm_adaptedPrefixWitness_le_one
#print axioms adaptedPrefixWitness_on_history
#print axioms gaussianRowSum_eq_fin_sum
#print axioms prefixWitnessCross_eq_rowSum
#print axioms measurable_prefixWitnessCross
#print axioms prefixWitnessCross_lower_tail
end GaussianEllipsoid
