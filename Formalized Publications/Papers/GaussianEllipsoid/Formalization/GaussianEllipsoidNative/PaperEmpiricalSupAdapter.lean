import UCUniformContinuity
import Mathlib.Data.EReal.Basic

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianEllipsoid.PaperEmpiricalSupAdapter
open UCUniformContinuity

/-- Literal normalized centered Gaussian rank-one matrix from the paper. -/
def centeredOuter {p : ℕ} (x : Vector p) : Square p := fun i j =>
  (x i*x j-(if i=j then 1 else 0))/Real.sqrt 2

theorem centeredOuter_transpose {p : ℕ} (x : Vector p) :
    (centeredOuter x).transpose=centeredOuter x := by
  classical
  ext i j
  simp only [Matrix.transpose_apply,centeredOuter,mul_comm,eq_comm]

/-- Explicit row-pairing bridge, with the paper's sqrt(2) normalization. -/
theorem centeredOuter_pairing {p : ℕ} (x : Vector p) (A : Square p) :
    (∑ i, ∑ j, centeredOuter x i j*A i j) =
      (quadratic A x-Matrix.trace A)/Real.sqrt 2 := by
  classical
  have hq : (∑ i, ∑ j, (x i*x j)*A i j) = quadratic A x := by
    unfold quadratic Matrix.mulVec dotProduct
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have ht : (∑ i, ∑ j, (if i=j then (1:ℝ) else 0)*A i j) = Matrix.trace A := by
    simp [Matrix.trace,Matrix.diag,ite_mul]
  simp only [centeredOuter,div_mul_eq_mul_div,← Finset.sum_div,sub_mul,
    Finset.sum_sub_distrib]
  rw [hq,ht]

theorem measurementQ_eq_pairing {p n : ℕ} (x : Sample p n) (A : Square p) (i : Fin n) :
    measurementQ x A i = ∑ a, ∑ b, centeredOuter (x i) a b*A a b :=
  (centeredOuter_pairing (x i) A).symm

/-- EReal supremum keeps the literal supremum exceptional event well-defined. -/
def empiricalSup (p n : ℕ) (x : Sample p n) : EReal :=
  sSup {t : EReal | ∃ A : Square p, A.transpose=A ∧ frobeniusNorm A=1 ∧
    t=((1/(n:ℝ))*∑ i, |measurementQ x A i| : ℝ)}

theorem empiricalSup_gt_iff (p n : ℕ) (C : ℝ) (x : Sample p n) :
    (C:EReal) < empiricalSup p n x ↔ ∃ A : Square p,
      A.transpose=A ∧ frobeniusNorm A=1 ∧ C < (1/(n:ℝ))*∑ i, |measurementQ x A i| := by
  rw [empiricalSup,lt_sSup_iff]
  constructor
  · rintro ⟨t,⟨A,hA,hF,rfl⟩,ht⟩
    exact ⟨A,hA,hF,EReal.coe_lt_coe_iff.mp ht⟩
  · rintro ⟨A,hA,hF,ht⟩
    exact ⟨_,⟨A,hA,hF,rfl⟩,EReal.coe_lt_coe_iff.mpr ht⟩

/-- Paper Lemma average_z_bound, with a universal c2=1 and A* depending
only on epsilon. The existing exp(-n) estimate is stronger than displayed. -/
theorem paper_average_z_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Astar : ℝ, 0 < Astar ∧ ∀ p n : ℕ, 0 < p →
      (1/4+ε)*(p:ℝ)^2 ≤ n →
      (gaussianSampleLaw p n).real {x | (Astar:EReal) < empiricalSup p n x} ≤
        2*Real.exp (-(1/4+ε)*(p:ℝ)^2) := by
  let a := 1/4+ε
  have ha : 0 < a := by dsimp [a]; linarith
  refine ⟨continuityConstant a,continuityConstant_pos ha,?_⟩
  intro p n hp hnlo
  have hn : 0 < n := by
    have hpos : (0:ℝ) < n := (mul_pos ha (sq_pos_of_pos (Nat.cast_pos.mpr hp))).trans_le hnlo
    exact_mod_cast hpos
  have hsub : {x : Sample p n | (continuityConstant a:EReal) < empiricalSup p n x} ⊆
      {x | ∃ A : Square p, A.transpose=A ∧ continuityConstant a*frobeniusNorm A <
        (1/(n:ℝ))*∑ i, |measurementQ x A i|} := by
    intro x hx
    obtain ⟨A,hA,hF,hbad⟩ := (empiricalSup_gt_iff p n (continuityConstant a) x).mp hx
    exact ⟨A,hA,by simpa only [hF,mul_one] using hbad⟩
  calc
    _ ≤ Real.exp (-(n:ℝ)) := (measureReal_mono hsub).trans (uniform_frobenius_l1_tail ha hp hn hnlo)
    _ ≤ Real.exp (-a*(p:ℝ)^2) := Real.exp_le_exp.mpr (by dsimp [a]; nlinarith)
    _ ≤ _ := by change Real.exp (-a*(p:ℝ)^2) ≤ 2*Real.exp (-a*(p:ℝ)^2); nlinarith [Real.exp_pos (-a*(p:ℝ)^2)]

#print axioms centeredOuter_pairing
#print axioms paper_average_z_bound
end GaussianEllipsoid.PaperEmpiricalSupAdapter
