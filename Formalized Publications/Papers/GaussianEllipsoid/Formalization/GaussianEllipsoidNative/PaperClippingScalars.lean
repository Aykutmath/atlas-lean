import ClippingConsequences
import GaussianEllipsoid.BelowObjects

noncomputable section
open scoped BigOperators
open GaussianMixedNormHelpers
namespace GaussianEllipsoid

theorem mixedNorm_eq_clipping_cost (η : ℝ) (d n : ℕ) (y : Vector n) :
    mixedNorm η d n y = infimalCost (η*Real.sqrt d) d y := rfl

theorem paper_q_range {d n : ℕ} (hd : 0 < d) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (y : Vector n) (hy : euclidNorm y=1) :
    η/Real.sqrt d ≤ mixedNorm η d n y/d ∧ mixedNorm η d n y/d ≤ 1 := by
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hs : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdR
  have hl := mixed_cost_lower hd hη.le hη1 y
  change η*Real.sqrt d*euclidNorm y ≤ mixedNorm η d n y at hl
  rw [hy,mul_one] at hl
  have hu : mixedNorm η d n y ≤ d := by
    rw [mixedNorm_eq_clipping_cost]
    have h := infimalCost_le_decomposition (a := η*Real.sqrt d) (b := (d:ℝ))
      (by positivity) hdR.le (u := 0) (v := y) (by simp : y=0+y)
    simpa [l1,show l2 y=1 from hy] using h
  constructor
  · apply (le_div_iff₀ hdR).mpr
    have he : η/Real.sqrt d*(d:ℝ)=η*Real.sqrt d := by
      apply (div_mul_eq_mul_div _ _ _).trans
      apply (div_eq_iff hs.ne').mpr
      nlinarith [Real.sq_sqrt hdR.le]
    simpa [he] using hl
  · exact (div_le_iff₀ hdR).mpr (by simpa using hu)

/-- The beta-relative coordinate cap used in the diffuse branch. -/
theorem paper_beta_relative_cap {d n : ℕ} (hd : 0 < d) {η β q : ℝ}
    (hη : 0 ≤ η) (hβ : 0 < β) (V : Vector n)
    (hcap : ∀ i, Real.sqrt d*|V i| ≤ η*q) (hlarge : β*q ≤ euclidNorm V) :
    Real.sqrt d*‖V‖ ≤ (η/β)*euclidNorm V := by
  have hs : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hright : 0 ≤ (η/β)*euclidNorm V := mul_nonneg (div_nonneg hη hβ.le) (euclidNorm_nonneg V)
  have hnorm : ‖V‖ ≤ ((η/β)*euclidNorm V)/Real.sqrt d := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hright hs.le)).mpr
    intro i
    apply (le_div_iff₀ hs).mpr
    rw [Real.norm_eq_abs]
    have hq : q ≤ euclidNorm V/β := (le_div_iff₀ hβ).mpr (by simpa [mul_comm] using hlarge)
    have hh := (hcap i).trans (mul_le_mul_of_nonneg_left hq hη)
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hh := (le_div_iff₀ hs).mp hnorm
  nlinarith

/-- Export the exact quotient deficit identity while retaining the original
optimizer v. This was previously only an internal multiplied equality. -/
theorem paper_optimizer_quotient_identity {n : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) {y u v : Fin n → ℝ}
    (hy : y=u+v) (hcost : infimalCost a b y=a*l1 u+b*l2 v)
    (hm : ∀ i, v i*u i=(a/b)*l2 v*|u i|) (hv : 0 < l2 v) :
    let I := Finset.univ.filter (fun i => u i ≠ 0)
    a*l1 (restrictCoords I y)=infimalCost a b y-b*l2 (restrictCoords Iᶜ y)^2/l2 v := by
  classical
  dsimp
  let I := Finset.univ.filter (fun i => u i ≠ 0)
  have hV : restrictCoords Iᶜ y=restrictCoords Iᶜ v := by
    ext i
    by_cases hu : u i=0 <;> simp [I,restrictCoords,hy,hu]
  have hU := l1_head_identity ha hb hy hm
  have henergy := head_energy_identity ha hb u v hm
  have hsplit : l2 (restrictCoords I v)^2+l2 (restrictCoords Iᶜ y)^2=l2 v^2 := by
    rw [hV,l2_sq,l2_sq,l2_sq]
    exact energy_restrict_add_compl I v
  change a*l1 (restrictCoords I y)=_
  change l1 (restrictCoords I y)=l1 u+l1 (restrictCoords I v) at hU
  change b*energy (restrictCoords I v)=a*l2 v*l1 (restrictCoords I v) at henergy
  rw [← l2_sq] at henergy
  apply (mul_right_cancel₀ hv.ne')
  rw [sub_mul,div_mul_cancel₀ _ hv.ne']
  rw [hU,hcost]
  nlinarith [henergy,congrArg (fun z : ℝ => b*z) hsplit]
/-- Scalar subgradient membership expressed by its defining supporting-line
inequality, retaining the original optimizer and no differentiability shortcut. -/
theorem paper_optimizer_coordinate_subgradient {n : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (u v : Fin n → ℝ)
    (hcap : ∀ i, |v i| ≤ (a/b)*l2 v)
    (hm : ∀ i, v i*u i=(a/b)*l2 v*|u i|) (hv : 0 < l2 v) :
    ∀ i z, a*|z| ≥ a*|u i|+(b*v i/l2 v)*(z-u i) := by
  intro i z
  have hp : |b*v i/l2 v| ≤ a := by
    rw [abs_div,abs_mul,abs_of_pos hb,abs_of_pos hv]
    apply (div_le_iff₀ hv).mpr
    have h := mul_le_mul_of_nonneg_left (hcap i) hb.le
    have he : b*((a/b)*l2 v)=a*l2 v := by field_simp
    simpa [he] using h
  have hm' : (b*v i/l2 v)*u i=a*|u i| := by
    apply (mul_right_cancel₀ hv.ne')
    field_simp
    have h := congrArg (fun z : ℝ => b*z) (hm i)
    field_simp at h
    nlinarith
  have hz := (le_abs_self ((b*v i/l2 v)*z)).trans
    ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hp (abs_nonneg z)))
  rw [mul_sub,hm']
  linarith

/-- Existence keeps the original minimizing v and the exact disjoint quotient
identity together, instead of forgetting v in the disjointization API. -/
theorem exists_paper_optimizer_with_quotient {n : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (y : Fin n → ℝ) :
    ∃ u v : Fin n → ℝ, y=u+v ∧
      infimalCost a b y=a*l1 u+b*l2 v ∧
      ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ (b/a)^2 ∧
      (∀ i, |v i| ≤ (a/b)*l2 v) ∧
      (∀ i, v i*u i=(a/b)*l2 v*|u i|) ∧
      (0 < l2 v → let I := Finset.univ.filter (fun i => u i ≠ 0);
        a*l1 (restrictCoords I y)=infimalCost a b y-b*l2 (restrictCoords Iᶜ y)^2/l2 v) := by
  obtain ⟨u,v,hy,hcost,hcard,hcap,hm⟩ := exists_optimal_sparse_capped_decomposition ha hb y
  exact ⟨u,v,hy,hcost,hcard,hcap,hm,paper_optimizer_quotient_identity ha.le hb hy hcost hm⟩
/-- The zero-tail optimizer branch has the literal l1 supporting functional
with the required Euclidean norm and unit signs on its support. -/
theorem paper_zero_tail_subgradient {n : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (y : Fin n → ℝ)
    (hcard : ((Finset.univ.filter (fun i => y i ≠ 0)).card:ℝ) ≤ (b/a)^2) :
    ∃ s : Fin n → ℝ, a*l2 s ≤ b ∧
      (∀ i, y i ≠ 0 → |s i|=1) ∧
      ∀ z : Fin n → ℝ, l1 y+(∑ i, s i*(z i-y i)) ≤ l1 z := by
  classical
  let s : Fin n → ℝ := fun i => if y i=0 then 0 else if 0 < y i then 1 else -1
  have hsq : l2 s^2=((Finset.univ.filter (fun i => y i ≠ 0)).card:ℝ) := by
    rw [l2_sq]
    unfold energy
    calc (∑ i, s i^2) = ∑ i : Fin n, if y i ≠ 0 then (1:ℝ) else 0 := by
           apply Finset.sum_congr rfl
           intro i _
           by_cases hy : y i=0 <;> by_cases hp : 0 < y i <;> simp [s,hy,hp]
      _ = _ := Finset.sum_boole _ _
  have hnorm : a*l2 s ≤ b := by
    apply (sq_le_sq₀ (mul_nonneg ha.le (l2_nonneg s)) hb.le).mp
    rw [mul_pow,hsq]
    have hh := mul_le_mul_of_nonneg_left hcard (sq_nonneg a)
    have he : a^2*(b/a)^2=b^2 := by field_simp
    simpa [he] using hh
  refine ⟨s,hnorm,?_,?_⟩
  · intro i hi
    by_cases hp : 0 < y i <;> simp [s,hi,hp]
  · intro z
    have hh : ∀ i, |y i|+s i*(z i-y i) ≤ |z i| := by
      intro i
      by_cases hy : y i=0
      · simp [s,hy]
      · by_cases hp : 0 < y i
        · simpa [s,hy,hp,abs_of_pos hp] using le_abs_self (z i)
        · have hn : y i ≤ 0 := le_of_not_gt hp
          simp only [s,if_neg hy,if_neg hp,abs_of_nonpos hn]
          nlinarith [neg_le_abs (z i)]
    simpa only [l1,Finset.sum_add_distrib] using Finset.sum_le_sum (fun i _ => hh i)
end GaussianEllipsoid
#print axioms GaussianEllipsoid.paper_q_range
#print axioms GaussianEllipsoid.paper_beta_relative_cap
#print axioms GaussianEllipsoid.paper_optimizer_quotient_identity
#print axioms GaussianEllipsoid.paper_optimizer_coordinate_subgradient
#print axioms GaussianEllipsoid.exists_paper_optimizer_with_quotient
#print axioms GaussianEllipsoid.paper_zero_tail_subgradient
