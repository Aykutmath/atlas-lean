import UCContinuityGeometry
import UCQuadraticSampleTail

/-! The actual uniform empirical Frobenius-to-l1 continuity event, with an
exponent proportional to n and hence to d² on every fixed positive aspect. -/
noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators
namespace GaussianEllipsoid.UCUniformContinuity
open UCContinuityGeometry

def continuityConstant (a : ℝ) : ℝ := 16*(3+5/a)

 theorem continuityConstant_pos {a : ℝ} (ha : 0 < a) : 0 < continuityConstant a := by
  unfold continuityConstant
  positivity

 theorem five_pow_le_exp (d : ℕ) : (5:ℝ)^(d*d) ≤ Real.exp (5*(d:ℝ)^2) := by
  have h5 : (5:ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5:ℝ)]
  calc
    _ ≤ (Real.exp 5)^(d*d) := pow_le_pow_left₀ (by norm_num) h5 _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- Explicit entropy calibration: the fixed half-net cost is absorbed by
choosing a fixed continuity constant depending only on the aspect floor. -/
theorem continuity_exponent {a : ℝ} (ha : 0 < a) {d n : ℕ}
    (haspect : a*(d:ℝ)^2 ≤ n) :
    5*(d:ℝ)^2+(n:ℝ)*(2-continuityConstant a/16) ≤ -(n:ℝ) := by
  have hratio : (d:ℝ)^2 ≤ (n:ℝ)/a := (le_div_iff₀ ha).mpr (by nlinarith)
  have h := mul_le_mul_of_nonneg_left hratio (by norm_num : (0:ℝ)≤5)
  unfold continuityConstant
  have he : 2-16*(3+5/a)/16 = -1-5/a := by ring
  rw [he]
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

/-- Kernel-checked actual probability bound for the Frobenius-to-l1 operator.
Every net center and every scalar tail is supplied by proved theorems. -/
theorem empiricalOperator_tail {a : ℝ} (ha : 0 < a) {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (haspect : a*(d:ℝ)^2 ≤ n) :
    (gaussianSampleLaw d n).real {x | continuityConstant a < ‖empiricalOperator x‖} ≤
      Real.exp (-(n:ℝ)) := by
  obtain ⟨s, hs, hcard, hnet⟩ := exists_half_net d
  let bad : SymFrob d → Set (Sample d n) := fun B =>
    {x | continuityConstant a/2 < (1/(n:ℝ))*∑ i, |measurementQ x (matrix B) i|}
  have hsub : {x : Sample d n | continuityConstant a < ‖empiricalOperator x‖} ⊆ ⋃ B ∈ s, bad B := by
    intro x hx
    by_contra hnot
    have hb : ∀ B ∈ s, (1/(n:ℝ))*∑ i, |measurementQ x (matrix B) i| ≤ continuityConstant a/2 := by
      intro B hB
      by_contra hlt
      apply hnot
      exact Set.mem_iUnion_of_mem B (Set.mem_iUnion_of_mem hB (lt_of_not_ge hlt))
    have hnorm := operator_le_twice_net x s hnet (continuityConstant a/2)
      (by positivity [continuityConstant_pos ha]) hb
    change continuityConstant a < ‖empiricalOperator x‖ at hx
    linarith
  have hp (B : SymFrob d) (hB : B ∈ s) :
      (gaussianSampleLaw d n).real (bad B) ≤ Real.exp ((n:ℝ)*(2-continuityConstant a/16)) := by
    have h := UCQuadraticSampleTail.sample_mean_abs_tail hd hn (matrix B) (matrix_transpose B)
      (by rw [matrix_frobeniusNorm, hs B hB]) (continuityConstant a/2)
    exact h.trans_eq (by congr 1; ring)
  calc
    _ ≤ (gaussianSampleLaw d n).real (⋃ B ∈ s, bad B) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ B ∈ s, (gaussianSampleLaw d n).real (bad B) := measureReal_biUnion_finset_le s bad
    _ ≤ ∑ _B ∈ s, Real.exp ((n:ℝ)*(2-continuityConstant a/16)) :=
      Finset.sum_le_sum fun B hB => hp B hB
    _ = (s.card:ℝ)*Real.exp ((n:ℝ)*(2-continuityConstant a/16)) := by simp
    _ ≤ Real.exp (5*(d:ℝ)^2)*Real.exp ((n:ℝ)*(2-continuityConstant a/16)) :=
      mul_le_mul_of_nonneg_right (hcard.trans (five_pow_le_exp d)) (Real.exp_nonneg _)
    _ = Real.exp (5*(d:ℝ)^2+(n:ℝ)*(2-continuityConstant a/16)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (continuity_exponent ha haspect)

/-- Exact embedding of a source symmetric matrix into the Frobenius domain. -/
def ofMatrix {d : ℕ} (A : Square d) (hA : A.transpose = A) : SymFrob d :=
  ⟨operatorFrobenius (Matrix.toEuclideanCLM (𝕜 := ℝ) A), by
    change (frobeniusOperator (operatorFrobenius (Matrix.toEuclideanCLM (𝕜 := ℝ) A))).toLinearMap.IsSymmetric
    rw [frobeniusOperator_operatorFrobenius]
    exact BMQuadraticSpectral.matrixSymmetric hA⟩

@[simp] theorem matrix_ofMatrix {d : ℕ} (A : Square d) (hA : A.transpose = A) :
    matrix (ofMatrix A hA) = A := by
  ext i j
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) A (EuclideanSpace.basisFun (Fin d) ℝ j)) i = A i j
  simp [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]

@[simp] theorem norm_ofMatrix {d : ℕ} (A : Square d) (hA : A.transpose = A) :
    ‖ofMatrix A hA‖ = frobeniusNorm A := by
  rw [← matrix_frobeniusNorm, matrix_ofMatrix]

/-- Every actual symmetric matrix is controlled by the one empirical operator. -/
theorem empirical_mean_le_operator {d n : ℕ} (x : Sample d n) (A : Square d) (hA : A.transpose = A) :
    (1/(n:ℝ))*∑ i, |measurementQ x A i| ≤ ‖empiricalOperator x‖*frobeniusNorm A := by
  have h := (empiricalOperator x).le_opNorm (ofMatrix A hA)
  simpa only [empiricalOperator_norm, matrix_ofMatrix, norm_ofMatrix] using h

/-- Full actual uniform continuity event in the project's matrix/sample types. -/
theorem uniform_frobenius_l1_tail {a : ℝ} (ha : 0 < a) {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (haspect : a*(d:ℝ)^2 ≤ n) :
    (gaussianSampleLaw d n).real {x | ∃ A : Square d, A.transpose = A ∧
      continuityConstant a*frobeniusNorm A < (1/(n:ℝ))*∑ i, |measurementQ x A i|} ≤
        Real.exp (-(n:ℝ)) := by
  apply le_trans (measureReal_mono (μ := gaussianSampleLaw d n) ?_)
    (empiricalOperator_tail ha hd hn haspect)
  rintro x ⟨A, hA, hbad⟩
  change continuityConstant a < ‖empiricalOperator x‖
  have h := empirical_mean_le_operator x A hA
  by_contra hnot
  have hu := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) (frobeniusNorm_nonneg A)
  linarith

#print axioms empiricalOperator_tail
#print axioms uniform_frobenius_l1_tail
end GaussianEllipsoid.UCUniformContinuity
