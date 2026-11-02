import PaperNuisanceNet
import UCDiffuseParameters

noncomputable section
open Module
namespace GaussianEllipsoid.PaperL1Entropy
open UCDiffuseParameters UCRationalLoss UCUniformContinuity

def entropyConstant (r B s : ℝ) : ℝ :=
  4*Real.log (1+2/r)+Real.log (1+2*B/s)+1

/-- Exact intrinsic nuisance entropy cost is independent of sample size. -/
theorem combined_entropy {d n : ℕ} {r B s : ℝ}
    (hr : 0 < r) (hB : 0 ≤ B) (hs : 0 < s)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (haspect : (1/4:ℝ)*(d:ℝ)^2 ≤ n)
    (I J : ℕ) (hI : 0 < I) (hJ : 0 < J)
    (hIc : (I:ℝ) ≤ (1+2/r)^(d*d))
    (hJc : (J:ℝ) ≤ (1+2*B/s)^(finrank ℝ L)) :
    Real.log ((I*J:ℕ):ℝ) ≤ entropyConstant r B s*(n:ℝ) := by
  have hb : 0 < 1+2/r := by positivity
  have hc : 0 < 1+2*B/s := by positivity
  have hi0 : (0:ℝ) < I := by exact_mod_cast hI
  have hj0 : (0:ℝ) < J := by exact_mod_cast hJ
  have hli := Real.log_le_log hi0 hIc
  have hlj := Real.log_le_log hj0 hJc
  rw [Real.log_pow] at hli hlj
  have hlogr : 0 ≤ Real.log (1+2/r) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hlogs : 0 ≤ Real.log (1+2*B/s) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hdim : (finrank ℝ L:ℝ) ≤ n := by
    have h := Submodule.finrank_le L
    simpa only [finrank_euclideanSpace_fin] using (show (finrank ℝ L:ℝ) ≤ finrank ℝ (EuclideanSpace ℝ (Fin n)) by exact_mod_cast h)
  have hmat := mul_le_mul_of_nonneg_right haspect hlogr
  have hnui := mul_le_mul_of_nonneg_right hdim hlogs
  have hli' : Real.log (I:ℝ) ≤ (d:ℝ)^2*Real.log (1+2/r) := by
    simpa only [Nat.cast_mul, pow_two] using hli
  rw [Nat.cast_mul, Real.log_mul hi0.ne' hj0.ne']
  unfold entropyConstant
  nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

theorem exists_parameters (θ B : ℝ) (hθ : 0 < θ) (hB : 0 ≤ B) :
    ∃ r s β τ : ℝ, 0 < r ∧ 0 < s ∧ 0 < β ∧ 0 < τ ∧ τ ≤ 1 ∧
      continuityConstant (1/4)*r+s ≤ 3*θ/16 ∧
      entropyConstant r B s ≤ (θ/16)*β ∧
      ∀ hβ : 0 ≤ β, normalizedComparisonConstant β hβ*τ ≤ θ/16 := by
  let C := continuityConstant (1/4)
  have hC : 0 < C := continuityConstant_pos (by norm_num)
  let r := θ/(64*(C+1))
  let s := θ/64
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hE : 0 < entropyConstant r B s := by
    have hl : 0 ≤ Real.log (1+2/r) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hl2 : 0 ≤ Real.log (1+2*B/s) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    unfold entropyConstant
    linarith
  let β := 1+16*entropyConstant r B s/θ
  have hβ : 0 < β := by dsimp [β]; positivity
  let K := normalizedComparisonConstant β hβ.le
  have hK : 0 ≤ K := normalizedComparisonConstant_nonneg β hβ.le
  let τ := min 1 (θ/(16*(K+1)))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  refine ⟨r,s,β,τ,hr,hs,hβ,hτ,min_le_left _ _,?_,?_,?_⟩
  · have hCr : C*r ≤ θ/64 := by
      have hc : C ≤ C+1 := by linarith
      have h := mul_le_mul_of_nonneg_right hc hr.le
      have he : (C+1)*r = θ/64 := by dsimp [r]; field_simp <;> ring
      rw [he] at h
      exact h
    change C*r+s ≤ _
    dsimp [s]
    linarith
  · dsimp [β]
    have ht : θ ≠ 0 := ne_of_gt hθ
    field_simp
    nlinarith
  · intro hβ'
    have ht : τ ≤ θ/(16*(K+1)) := min_le_right _ _
    have ht' := (le_div_iff₀ (by positivity : (0:ℝ)<16*(K+1))).mp ht
    change normalizedComparisonConstant β hβ'*τ ≤ _
    have he : normalizedComparisonConstant β hβ' = K := rfl
    rw [he]
    nlinarith


#print axioms exists_parameters
#print axioms combined_entropy
end GaussianEllipsoid.PaperL1Entropy
