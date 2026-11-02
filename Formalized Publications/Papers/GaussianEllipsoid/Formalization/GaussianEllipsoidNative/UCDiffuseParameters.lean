import UCRationalLoss
import UCUniformContinuity
import UCDiffuseNets

/-! Fixed parameters in the noncircular order: Gaussian loss margin, meshes,
temperature, operator cap. Nuisance rank affects only the eventual threshold. -/
noncomputable section
open Filter
open scoped Topology
namespace GaussianEllipsoid.UCDiffuseParameters
open UCRationalLoss UCUniformContinuity

 def entropyConstant (r : ℝ) : ℝ := 4*Real.log (1+2/r)+1

/-- Every positive Gaussian rational-loss margin has fixed positive meshes,
a fixed temperature, and a fixed diffuse cap satisfying all comparison and
entropy budgets. None depends on nuisance rank or sample dimension. -/
theorem exists_parameters (θ : ℝ) (hθ : 0 < θ) :
    ∃ r s β τ : ℝ, 0 < r ∧ 0 < s ∧ 0 < β ∧ 0 < τ ∧ τ ≤ 1 ∧
      continuityConstant (1/4)*r+s ≤ 3*θ/16 ∧
      entropyConstant r ≤ (θ/16)*β ∧
      ∀ hβ : 0 ≤ β, normalizedComparisonConstant β hβ*τ ≤ θ/16 := by
  let C := continuityConstant (1/4)
  have hC : 0 < C := continuityConstant_pos (by norm_num)
  let r := θ/(64*(C+1))
  let s := θ/64
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hE : 0 < entropyConstant r := by
    have hl : 0 ≤ Real.log (1+2/r) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    unfold entropyConstant
    linarith
  let β := 1+16*entropyConstant r/θ
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

/-- Transferring an eventual sample-count fact to every sample count in the
positive-aspect cone, with full uniform quantifiers. -/
theorem eventually_forall_quarter_square {P : ℕ → Prop} (hP : ∀ᶠ n : ℕ in atTop, P n) :
    ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, (1/4:ℝ)*(d:ℝ)^2 ≤ n → P n := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hP
  filter_upwards [eventually_ge_atTop (4*N+1)] with d hd
  intro n hn
  apply hN
  have hd' : (4:ℝ)*N+1 ≤ d := by exact_mod_cast hd
  have hd0 : (1:ℝ) ≤ d := by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hsq : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hn' : (N:ℝ) ≤ n := by nlinarith
  exact_mod_cast hn'

/-- A sum of the two proved exponential failure terms remains exponential
in d² on the quarter-aspect cone. -/
theorem exponential_pair_eventually (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop, ∀ n : ℕ,
      (1/4:ℝ)*(d:ℝ)^2 ≤ n →
      Real.exp (-(n:ℝ))+Real.exp (-(n:ℝ)*θ^2/128) ≤ Real.exp (-C*(d:ℝ)^2) := by
  let k := min 1 (θ^2/128)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k/8,by positivity,?_⟩
  have hN : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ k*(n:ℝ)/2 := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (2*Real.log 2/k)] with n hn
    have hn' := (div_le_iff₀ hk).mp hn
    nlinarith
  filter_upwards [eventually_forall_quarter_square hN] with d hd
  intro n hn
  have he1 : Real.exp (-(n:ℝ)) ≤ Real.exp (-k*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (1:ℝ) (θ^2/128), (Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  have he2 : Real.exp (-(n:ℝ)*θ^2/128) ≤ Real.exp (-k*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (1:ℝ) (θ^2/128), (Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  have hlog := hd n hn
  calc
    _ ≤ 2*Real.exp (-k*(n:ℝ)) := by linarith
    _ = Real.exp (Real.log 2-k*(n:ℝ)) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num),
        show -k*(n:ℝ) = -(k*(n:ℝ)) by ring, Real.exp_neg]
      ring
    _ ≤ Real.exp (-k*(n:ℝ)/2) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hn hk.le])

#print axioms exists_parameters
#print axioms exponential_pair_eventually
end GaussianEllipsoid.UCDiffuseParameters
