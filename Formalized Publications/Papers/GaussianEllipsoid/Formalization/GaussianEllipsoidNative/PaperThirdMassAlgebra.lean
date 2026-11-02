import PaperCavityPrior
import PaperGibbsThird

/-! Newly reconstructed bounded-function replica algebra. PaperTensorMass and
PaperGibbsThirdTest are explicitly reconstructed transitive support namespaces.
All components use genuine bounded continuous functions and their sup norms. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators BoundedContinuousFunction
namespace PaperTensorMass
variable {κ E : Type*} [Fintype κ] [DecidableEq κ]
variable [NormedAddCommGroup E]

def mass (T : κ → κ → κ → E) : ℝ := ∑ a, ∑ b, ∑ c, ‖T a b c‖
def diagonal (x : κ → E) (a b c : κ) : E := if a=b ∧ a=c then x a else 0

theorem mass_add_le (S T : κ → κ → κ → E) :
    mass (S+T) ≤ mass S + mass T := by
  unfold mass
  simp only [Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
    Finset.sum_le_sum fun _ _ => norm_add_le _ _

theorem mass_sub_le (S T : κ → κ → κ → E) :
    mass (S-T) ≤ mass S + mass T := by
  unfold mass
  simp only [Pi.sub_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
    Finset.sum_le_sum fun _ _ => norm_sub_le _ _

theorem mass_diagonal (x : κ → E) : mass (diagonal x) = ∑ a, ‖x a‖ := by
  simp [mass, diagonal, apply_ite norm, ite_and]

variable [NormedSpace ℝ E]
theorem mass_smul (r : ℝ) (T : κ → κ → κ → E) :
    mass (r • T) = |r| * mass T := by
  simp only [mass, Pi.smul_apply, norm_smul, Real.norm_eq_abs, ← Finset.mul_sum]

end PaperTensorMass
namespace PaperThirdMassAlgebra
open PaperTensorMass PaperCavityPrior
variable {κ X : Type*} [Fintype κ] [DecidableEq κ] [TopologicalSpace X]


def pairAB (x y : κ → (X →ᵇ ℝ)) (a b c : κ) : (X →ᵇ ℝ) := if a=b then x a*y c else 0
def pairAC (x y : κ → (X →ᵇ ℝ)) (a b c : κ) : (X →ᵇ ℝ) := if a=c then x a*y b else 0
def pairBC (x y : κ → (X →ᵇ ℝ)) (a b c : κ) : (X →ᵇ ℝ) := if b=c then y a*x b else 0
def triple (x : κ → (X →ᵇ ℝ)) (a b c : κ) : (X →ᵇ ℝ) := x a*x b*x c

def replicaTensor (β : ℝ) (p f g h : κ → (X →ᵇ ℝ)) : κ → κ → κ → (X →ᵇ ℝ) :=
  (-β) • diagonal (fun a => p a*h a) + β^2 •
    ((3 : ℝ) • diagonal (fun a => p a*g a*f a) -
      pairAB (fun a => p a*g a) (fun a => p a*f a) -
      pairAC (fun a => p a*g a) (fun a => p a*f a) -
      pairBC (fun a => p a*g a) (fun a => p a*f a)) - β^3 •
    (diagonal (fun a => p a*(f a)^3) -
      pairAB (fun a => p a*(f a)^2) (fun a => p a*f a) -
      pairAC (fun a => p a*(f a)^2) (fun a => p a*f a) -
      pairBC (fun a => p a*(f a)^2) (fun a => p a*f a) +
      (2 : ℝ) • (fun a b c => (p a*f a)*(p b*f b)*(p c*f c)))

lemma mass_pairAB_le (x y : κ → (X →ᵇ ℝ)) : mass (pairAB x y) ≤ priorMass x * priorMass y := by
  simp only [mass, pairAB, apply_ite norm, norm_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold priorMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => norm_mul_le _ _

lemma mass_pairAC_le (x y : κ → (X →ᵇ ℝ)) : mass (pairAC x y) ≤ priorMass x * priorMass y := by
  simp only [mass, pairAC, apply_ite norm, norm_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold priorMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => norm_mul_le _ _

lemma mass_pairBC_le (x y : κ → (X →ᵇ ℝ)) : mass (pairBC x y) ≤ priorMass x * priorMass y := by
  simp only [mass, pairBC, apply_ite norm, norm_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [mul_comm]
  unfold priorMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => norm_mul_le _ _

lemma mass_triple_le (x : κ → (X →ᵇ ℝ)) : mass (triple x) ≤ (priorMass x)^3 := by
  unfold mass triple priorMass
  have he : (∑ a, ‖x a‖)^3 = ∑ a, ∑ b, ∑ c, ‖x a‖*‖x b‖*‖x c‖ := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [he]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
    Finset.sum_le_sum fun _ _ => (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

lemma priorMass_mul_le (p f : κ → (X →ᵇ ℝ)) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ a, ‖f a‖ ≤ C) :
    priorMass (fun a => p a*f a) ≤ C*priorMass p := by
  unfold priorMass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => (norm_mul_le _ _).trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hf a) (norm_nonneg (p a)))

/-- Exact sparse replica coefficient mass, with no cardinality factor. -/
theorem replicaTensor_mass_le (β : ℝ) (p f g h : κ → (X →ᵇ ℝ))
    {C1 C2 C3 : ℝ} (hβ : 0 ≤ β) (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) (h3 : 0 ≤ C3)
    (hf : ∀ a, ‖f a‖ ≤ C1) (hg : ∀ a, ‖g a‖ ≤ C2) (hh : ∀ a, ‖h a‖ ≤ C3) :
    mass (replicaTensor β p f g h) ≤ β*C3*priorMass p +
      3*β^2*C1*C2*(priorMass p+(priorMass p)^2) +
      β^3*C1^3*(priorMass p+3*(priorMass p)^2+2*(priorMass p)^3) := by
  let P := priorMass p
  have hp : 0 ≤ P := priorMass_nonneg p
  have hf2 (a : κ) : ‖(f a)^2‖ ≤ C1^2 :=
    (norm_pow_le' _ (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg _) (hf a) 2)
  have hf3 (a : κ) : ‖(f a)^3‖ ≤ C1^3 :=
    (norm_pow_le' _ (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg _) (hf a) 3)
  have hpf := priorMass_mul_le p f h1 hf
  have hpg := priorMass_mul_le p g h2 hg
  have hph := priorMass_mul_le p h h3 hh
  have hpf2 := priorMass_mul_le p (fun a => (f a)^2) (sq_nonneg C1) hf2
  have hpf3 := priorMass_mul_le p (fun a => (f a)^3) (pow_nonneg h1 3) hf3
  have hpgf : priorMass (fun a => p a*g a*f a) ≤ C1*C2*P := by
    calc
      _ ≤ C1 * priorMass (fun a => p a*g a) := priorMass_mul_le _ f h1 hf
      _ ≤ C1*(C2*P) := mul_le_mul_of_nonneg_left hpg h1
      _ = _ := by ring
  have pair1 : ∀ T ∈ [pairAB, pairAC, pairBC],
      mass (T (fun a => p a*g a) (fun a => p a*f a)) ≤ C1*C2*P^2 := by
    intro T hT
    have hbound := (mul_le_mul hpg hpf (priorMass_nonneg _) (by positivity))
    have ht : mass (T (fun a => p a*g a) (fun a => p a*f a)) ≤
        priorMass (fun a => p a*g a)*priorMass (fun a => p a*f a) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl
      · exact mass_pairAB_le _ _
      · exact mass_pairAC_le _ _
      · exact mass_pairBC_le _ _
    exact ht.trans (by nlinarith)
  have pair2 : ∀ T ∈ [pairAB, pairAC, pairBC],
      mass (T (fun a => p a*(f a)^2) (fun a => p a*f a)) ≤ C1^3*P^2 := by
    intro T hT
    have hbound := mul_le_mul hpf2 hpf (priorMass_nonneg _) (by positivity)
    have ht : mass (T (fun a => p a*(f a)^2) (fun a => p a*f a)) ≤
        priorMass (fun a => p a*(f a)^2)*priorMass (fun a => p a*f a) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl
      · exact mass_pairAB_le _ _
      · exact mass_pairAC_le _ _
      · exact mass_pairBC_le _ _
    exact ht.trans (by nlinarith)
  have htrip : mass (triple (fun a => p a*f a)) ≤ C1^3*P^3 := by
    apply (mass_triple_le _).trans
    have hz := pow_le_pow_left₀ (priorMass_nonneg _) hpf 3
    simpa only [mul_pow] using hz
  unfold replicaTensor
  apply (mass_sub_le _ _).trans
  apply (add_le_add (mass_add_le _ _) le_rfl).trans
  simp only [mass_smul, abs_neg, abs_of_nonneg hβ, abs_pow]
  have hcov := mass_sub_le
    ((3 : ℝ) • diagonal (fun a => p a*g a*f a) - pairAB (fun a => p a*g a) (fun a => p a*f a) -
      pairAC (fun a => p a*g a) (fun a => p a*f a))
    (pairBC (fun a => p a*g a) (fun a => p a*f a))
  have hcov1 := mass_sub_le
    ((3 : ℝ) • diagonal (fun a => p a*g a*f a) - pairAB (fun a => p a*g a) (fun a => p a*f a))
    (pairAC (fun a => p a*g a) (fun a => p a*f a))
  have hcov2 := mass_sub_le ((3 : ℝ) • diagonal (fun a => p a*g a*f a))
    (pairAB (fun a => p a*g a) (fun a => p a*f a))
  have hcumul := mass_add_le
    (diagonal (fun a => p a*(f a)^3) - pairAB (fun a => p a*(f a)^2) (fun a => p a*f a) -
      pairAC (fun a => p a*(f a)^2) (fun a => p a*f a) -
      pairBC (fun a => p a*(f a)^2) (fun a => p a*f a))
    ((2 : ℝ) • triple (fun a => p a*f a))
  have hcum1 := mass_sub_le
    (diagonal (fun a => p a*(f a)^3) - pairAB (fun a => p a*(f a)^2) (fun a => p a*f a) -
      pairAC (fun a => p a*(f a)^2) (fun a => p a*f a))
    (pairBC (fun a => p a*(f a)^2) (fun a => p a*f a))
  have hcum2 := mass_sub_le
    (diagonal (fun a => p a*(f a)^3) - pairAB (fun a => p a*(f a)^2) (fun a => p a*f a))
    (pairAC (fun a => p a*(f a)^2) (fun a => p a*f a))
  have hcum3 := mass_sub_le (diagonal (fun a => p a*(f a)^3))
    (pairAB (fun a => p a*(f a)^2) (fun a => p a*f a))
  simp only [mass_smul, mass_diagonal, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at *
  have hp11 := pair1 pairAB (by simp)
  have hp12 := pair1 pairAC (by simp)
  have hp13 := pair1 pairBC (by simp)
  have hp21 := pair2 pairAB (by simp)
  have hp22 := pair2 pairAC (by simp)
  have hp23 := pair2 pairBC (by simp)
  change (∑ a, ‖p a*h a‖) ≤ _ at hph
  change (∑ a, ‖p a*g a*f a‖) ≤ _ at hpgf
  change (∑ a, ‖p a*(f a)^3‖) ≤ _ at hpf3
  have hcov' : mass
      ((3 : ℝ) • diagonal (fun a => p a*g a*f a) -
        pairAB (fun a => p a*g a) (fun a => p a*f a) -
        pairAC (fun a => p a*g a) (fun a => p a*f a) -
        pairBC (fun a => p a*g a) (fun a => p a*f a)) ≤
      3*C1*C2*(P+P^2) := by
    linarith
  have hcum' : mass
      (diagonal (fun a => p a*(f a)^3) -
        pairAB (fun a => p a*(f a)^2) (fun a => p a*f a) -
        pairAC (fun a => p a*(f a)^2) (fun a => p a*f a) -
        pairBC (fun a => p a*(f a)^2) (fun a => p a*f a) +
        (2 : ℝ) • triple (fun a => p a*f a)) ≤ C1^3*(P+3*P^2+2*P^3) := by
    linarith
  have hfirst := mul_le_mul_of_nonneg_left hph hβ
  have hsecond := mul_le_mul_of_nonneg_left hcov' (sq_nonneg β)
  have hthird := mul_le_mul_of_nonneg_left hcum' (pow_nonneg hβ 3)
  dsimp only [triple, P] at hfirst hsecond hthird ⊢
  exact (add_le_add (add_le_add hfirst hsecond) hthird).trans_eq (by ring)

#print axioms replicaTensor_mass_le
end PaperThirdMassAlgebra

namespace PaperGibbsThirdTest
open BMFiniteGibbsTest BMFiniteGibbsHessian PaperGibbsThird
open PaperThirdMassAlgebra PaperTensorMass
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def coordinate (a : κ) : C((κ → ℝ), ℝ) := ⟨fun y => y a, continuous_apply a⟩
def first (D : Data κ) (a : κ) : (κ → ℝ) →ᵇ ℝ := D.potentialDeriv.compContinuous (coordinate a)
def second (D : Data2 κ) (a : κ) : (κ → ℝ) →ᵇ ℝ := D.potentialSecond.compContinuous (coordinate a)
def third (D : Data3 κ) (a : κ) : (κ → ℝ) →ᵇ ℝ := D.potentialThird.compContinuous (coordinate a)

def boundedThird (D : Data3 κ) (a b c : κ) : (κ → ℝ) →ᵇ ℝ :=
  replicaTensor D.beta (boundedProbability D.toData) (first D.toData)
    (second D.toData2) (third D) a b c

theorem boundedThird_apply (D : Data3 κ) (a b c : κ) (y : κ → ℝ) :
    boundedThird D a b c y = PaperGibbsThird.third D a b c y := by
  rw [PaperGibbsThird.third_eq_replicaThird]
  by_cases hab : a=b <;> by_cases hac : a=c <;> by_cases hbc : b=c
  all_goals simp [boundedThird, replicaTensor, diagonal, pairAB, pairAC, pairBC,
    triple, boundedProbability, first, second, third, coordinate,
    replicaThird, hab, hac, hbc]
  all_goals ring <;> simp_all [eq_comm]

#print axioms boundedThird_apply
end PaperGibbsThirdTest
